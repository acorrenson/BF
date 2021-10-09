Require Import ZArith Lia Syntax Semantics.

Inductive aexpr :=
  | Cst : Z -> aexpr
  | Add : aexpr -> aexpr -> aexpr
  | Var : nat -> aexpr.

Inductive imp :=
  | Imp_Seq   : imp -> imp -> imp
  | Imp_Aff   : nat -> aexpr -> imp
  | Imp_While : aexpr -> imp -> imp.

Fixpoint eval (a : aexpr) (s : store) : Z :=
  match a with
  | Cst v => v
  | Add e1 e2 => eval e1 s + eval e2 s
  | Var x => s x
  end.


Inductive imp_exec : store -> imp -> store -> Prop :=
  | iexec_seq  : forall s1 s2 s3 p1 p2,
    imp_exec s1 p1 s2 ->
    imp_exec s2 p2 s3 ->
    imp_exec s1 (Imp_Seq p1 p2) s3
  | iexec_loop : forall s1 s2 s3 c p,
    eval c s1 <> 0%Z ->
    imp_exec s1 p s2 ->
    imp_exec s2 (Imp_While c p) s3 ->
    imp_exec s1 (Imp_While c p) s3
  | iexec_loop_done : forall s c p,
    eval c s = 0%Z ->
    imp_exec s (Imp_While c p) s.

Fixpoint compile_cst_pos (n : nat) : program :=
  match n with
  | O => Done
  | S m =>
    Seq Incr (compile_cst_pos m)
  end.

Fixpoint compile_cst_neg (n : nat) : program :=
  match n with
  | O => Done
  | S m =>
    Seq Decr (compile_cst_neg m)
  end.

Definition compile_cst (v : Z) : program :=
  if (0 <=? v)%Z then compile_cst_pos (Z.abs_nat v) else compile_cst_neg (Z.abs_nat v).

Definition Zneg (n : nat) : Z := - Z.of_nat n.

Definition Zpos (n : nat) := Z.of_nat n.

Lemma Zpos_abs :
  forall n, n = Z.abs_nat (Zpos n).
Proof.
  induction n; intros.
  + cbn; reflexivity.
  + cbn; destruct n; lia.
Qed.

Lemma Zneg_abs :
  forall n, n = Z.abs_nat (Zneg n).
Proof.
  induction n; intros.
  + cbn; reflexivity.
  + cbn; destruct n; lia.
Qed.

Lemma Zpos_succ :
  forall n, Zpos (S n) = (1 + Zpos n)%Z.
Proof.
  induction n; auto.
  rewrite IHn.
  unfold Zpos.
  repeat rewrite Nat2Z.inj_succ.
  lia.
Qed.

Lemma Zneg_pred :
  forall n, Zneg (S n) = (Zneg n - 1)%Z.
Proof.
  induction n; auto.
  rewrite IHn.
  unfold Zneg.
  repeat rewrite Nat2Z.inj_succ.
  lia.
Qed.

Lemma eval_succ :
  forall z s, (eval (Cst (1 + z)) s = 1 + eval (Cst z) s)%Z.
Proof.
  reflexivity.
Qed.

Lemma eval_pred :
  forall z s, (eval (Cst (z - 1)) s = eval (Cst z) s - 1)%Z.
Proof.
  reflexivity.
Qed.

Lemma eval_cst :
  forall v s s', eval (Cst v) s = eval (Cst v) s'.
Proof.
  reflexivity.
Qed.

Lemma get_val_incr :
  forall s, (1 + get_val s)%Z = get_val (incr s).
Proof.
  intros [ ].
  unfold incr.
  unfold get_val, store_incr, store_update.
  rewrite (Nat.eqb_refl).
  lia.
Qed.

Lemma get_val_decr :
  forall s, (get_val s - 1)%Z = get_val (decr s).
Proof.
  intros [ ].
  unfold decr, get_val, store_decr, store_update.
  rewrite (Nat.eqb_refl).
  lia.
Qed.

Lemma compile_cst_pos_correct :
  forall n s s',
  s -< compile_cst_pos n >-> s' ->
  (get_val s + eval (Cst (Zpos n)) (get_store s))%Z = get_val s'.
Proof.
  induction n; intros.
  - inversion_clear H.
    rewrite <- Z.add_comm.
    reflexivity.
  - cbn in H.
    inversion_clear H.
    inversion_clear H0.
    subst.
    pose proof (IHn _ _ H1).
    rewrite Zpos_succ, eval_succ, <- H.
    replace (get_val (incr s)) with (1 + get_val s)%Z by apply get_val_incr.
    replace (eval (Cst (Zpos n)) (get_store (incr s))) with (eval (Cst (Zpos n)) (get_store s)) by reflexivity.
    lia.
Qed.

Lemma compile_cst_neg_correct :
  forall n s s',
  s -< compile_cst_neg n >-> s' ->
  (get_val s + eval (Cst (Zneg n)) (get_store s))%Z = get_val s'.
Proof.
  induction n; intros.
  - inversion_clear H.
    subst.
    rewrite <- Z.add_comm.
    reflexivity.
  - cbn in H.
    inversion_clear H.
    inversion_clear H0.
    subst.
    pose proof (IHn _ _ H1).
    rewrite Zneg_pred, eval_pred, <- H.
    replace (get_val (decr s)) with (get_val s - 1)%Z by apply get_val_decr.
    replace (eval (Cst (Zneg n)) (get_store (decr s))) with (eval (Cst (Zneg n)) (get_store s)) by reflexivity.
    lia.
Qed.

Lemma compile_cst_correct :
  forall v s,
  state0 -< compile_cst v >-> s ->
  eval (Cst v) (get_store state0) = get_val s.
Proof.
  intros.
  destruct v.
  + now inversion_clear H.
  + cbn in H.
    rewrite <- (compile_cst_pos_correct _ _ _ H).
    simpl.
    unfold Zpos.
    now rewrite positive_nat_Z.
  + cbn in H.
    rewrite <- (compile_cst_neg_correct _ _ _ H).
    simpl.
    unfold Zneg.
    now rewrite positive_nat_Z.
Qed.