Require Import ZArith Lia.
Require Import FunctionalExtensionality.

(**
  The brainfuck language
*)
Inductive bf :=
  | Left  : bf
  | Right : bf
  | Incr  : bf
  | Decr  : bf
  | Seq   : bf -> bf -> bf
  | Loop  : bf -> bf.

(**
  Right-infinite memory
*)
Definition store : Type := nat -> Z.

(**
  A brainfuck state is composed of a data pointer and a store
*)
Definition state : Type := (nat * store)%type.

(**
  Update the memory
*)
Definition store_update (n : nat) (val : Z) (s : store) : store :=
  fun x => if x =? n then val else s x.

(**
  Increment a cell in memory
*)
Definition store_incr (n : nat) (s : store) : store :=
  store_update n ((s n) + 1) s.

(**
  Decrement a cell in memory
*)
Definition store_decr (n : nat) (s : store) : store :=
  store_update n ((s n) - 1) s.

(**
  Increment the current cell in a state
*)
Definition incr (s : state) :=
  let (dp, store) := s in
  (dp, store_incr dp store).

(**
  Decrement the current cell in a state
*)
Definition decr (s : state) :=
  let (dp, store) := s in
  (dp, store_decr dp store).

(**
  Move the data pointer to the left
*)
Definition left (s : state) :=
  let (dp, store) := s in
  (dp - 1, store).

(**
  Move the data pointer to the right
*)
Definition right (s : state) :=
  let (dp, store) := s in
  (dp + 1, store).

(**
  Update the current cell in the state
*)
Definition update (s : state) (val : Z) : state :=
  let (dp, store) := s in
  (dp, store_update dp val store).

(**
  Get the data pointer of a state
*)
Definition get_dp (s : state) : nat :=
  let (dp, _) := s in dp.

(**
  Get the memory of a state
*)
Definition get_store (s : state) : store :=
  let (_, store) := s in store.

(**
  Get the value of the current cell of a state
*)
Definition get_val (s : state) : Z :=
  let (dp, store) := s in store dp.

(**
  Big-step operationnal semantic of Brainfuck
*)
Inductive exec : state -> bf -> state -> Prop :=
  | exec_left : forall s s',
    get_dp s > 0 -> s' = left s -> exec s Left s'
  | exec_right : forall s s',
    s' = right s -> exec s Right s'
  | exec_incr  : forall s s',
    s' = incr s -> exec s Incr s'
  | exec_decr  : forall s s',
    s' = decr s -> exec s Decr s'
  | exec_loop  : forall b s s' s'',
    get_val s <> 0%Z ->
    exec s b s' ->
    exec s' (Loop b) s'' ->
    exec s (Loop b) s''
  | exec_loop_done : forall b s,
    get_val s = 0%Z ->
    exec s (Loop b) s
  | exec_seq : forall b1 b2 s1 s2 s3,
    exec s1 b1 s2 ->
    exec s2 b2 s3 ->
    exec s1 (Seq b1 b2) s3.

(* Inductive execs : state -> bf -> state -> Prop :=
  | exec_one : forall s1 s2 p,
    exec s1 p s2 -> execs s1 p s2
  | exec_trans : forall s1 s2 s3 p,
    exec s1 p s2 ->
    exec s2 p s3 ->
    execs s1 p s3. *)

Notation "a -< b >-> c" := (exec a b c) (at level 80).
Notation "a ';;' b" := (Seq a b) (at level 80).

Definition state0 : state := (0, fun x => 0%Z).

Lemma incr_decr_id:
  forall s, incr (decr s) = s.
Proof.
  intros (dp & store).
  apply pair_equal_spec; split.
  - reflexivity.
  - unfold store_incr, store_decr, store_update.
    apply functional_extensionality; intros.
    destruct (x =? dp) eqn:E; auto.
    rewrite beq_nat_true_iff in E; subst.
    rewrite <- beq_nat_refl; lia.
Qed.

Ltac state_eq :=
  match goal with
  | [ |- ?x = ?y ] =>
    apply pair_equal_spec; split; [
        try reflexivity | try reflexivity; (apply functional_extensionality; intros)
      ]
  end.

Lemma incr_decr_comm:
  forall s, incr (decr s) = decr (incr s).
Proof.
  intros (dp & store).
  state_eq.
  unfold store_incr, store_decr, store_update.
  destruct (_ =? _); auto.
  rewrite <- beq_nat_refl.
  lia.
Qed.

Lemma incr_decr_skip:
  exec state0 (Incr ;; Decr) state0.
Proof.
  eapply exec_seq.
  - apply exec_incr. reflexivity.
  - apply exec_decr.
    rewrite <- incr_decr_comm, incr_decr_id.
    reflexivity.
Qed.

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

Fixpoint compile_cst_pos (n : nat) : bf :=
  match n with
  | O => Incr ;; Decr
  | S m =>
    Incr ;; compile_cst_pos m
  end.

Fixpoint compile_cst_neg (n : nat) : bf :=
  match n with
  | O => Incr ;; Decr
  | S m =>
    Decr ;; compile_cst_neg m
  end.

  Search (Z -> nat).

Definition compile_cst (v : Z) : bf :=
  if (0 <=? v)%Z then compile_cst_pos (Z.abs_nat v) else compile_cst_neg (Z.abs_nat v).

Compute (Z.neg (Pos.of_nat 10)).

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


Lemma Zpos_S :
  forall n, Zpos (S n) = (1 + Zpos n)%Z.
Proof.
  induction n; auto.
  rewrite IHn.
  unfold Zpos.
  repeat rewrite Nat2Z.inj_succ.
  lia.
Qed.

Lemma Zneg_S :
  forall n, Zneg (S n) = (Zneg n - 1)%Z.
Proof.
  induction n; auto.
  rewrite IHn.
  unfold Zneg.
  repeat rewrite Nat2Z.inj_succ.
  lia.
Qed.

Lemma eval_S :
  forall z s, (eval (Cst (1 + z)) s = 1 + eval (Cst z) s)%Z.
Proof.
  reflexivity.
Qed.

Lemma eval_P :
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
    inversion_clear H0.
    inversion_clear H1.
    subst.
    rewrite <- Z.add_comm.
    simpl.
    now rewrite <- incr_decr_comm, incr_decr_id.
  - cbn in H.
    inversion_clear H.
    inversion_clear H0.
    subst.
    pose proof (IHn _ _ H1).
    rewrite Zpos_S, eval_S, <- H.
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
    inversion_clear H0.
    inversion_clear H1.
    subst.
    rewrite <- Z.add_comm.
    simpl.
    now rewrite <- incr_decr_comm, incr_decr_id.
  - cbn in H.
    inversion_clear H.
    inversion_clear H0.
    subst.
    pose proof (IHn _ _ H1).
    rewrite Zneg_S, eval_P, <- H.
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
  + inversion_clear H.
    inversion_clear H0.
    inversion_clear H1.
    subst.
    reflexivity.
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