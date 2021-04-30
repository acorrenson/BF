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