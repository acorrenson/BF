From Coq Require Import List String Byte Ascii.
From Bf Require Import Parser.
Import ListNotations.

Inductive program : Type :=
  | Seq : instruction -> program -> program
  | Done : program.

Fixpoint to_program l :=
  match l with
  | i::is => Seq i (to_program is)
  | [] => Done
  end.

Definition _parse (x : list byte) := bind (parse (string_of_list_byte x)) (fun x => Some (to_program x)).
Fixpoint _print_aux (n : nat) (x : program) :=
  match n with
  | O => None
  | S n => 
    match x with
    | Done => Some []
    | Seq Incr next =>
      bind (_print_aux n next) (fun r => Some (byte_of_ascii ("+"%char)::r))
    | Seq Decr next =>
      bind (_print_aux n next) (fun r => Some (byte_of_ascii ("-"%char)::r))
    | Seq Left next =>
      bind (_print_aux n next) (fun r => Some (byte_of_ascii ("<"%char)::r))
    | Seq Right next =>
      bind (_print_aux n next) (fun r => Some (byte_of_ascii (">"%char)::r))
    | Seq In next =>
      bind (_print_aux n next) (fun r => Some (byte_of_ascii (","%char)::r))
    | Seq Out next =>
      bind (_print_aux n next) (fun r => Some (byte_of_ascii ("."%char)::r))
    | Seq (Loop p) next =>
      bind (_print_aux n next) (fun r =>
        bind (_print_aux n (to_program p)) (fun r' =>
          Some ([byte_of_ascii "["%char] ++ r' ++ [byte_of_ascii "]"%char] ++ r)
      ))
    end
  end.

Definition _print (p : program) := _print_aux 1000 p.

Declare Scope bf.
Delimit Scope bf with bf.
String Notation program _parse _print : bf.

Notation "x ;; y" := (Seq x y) (right associativity, at level 100).

Example test :
  "++[<>.]"%bf = (
    Incr ;;
    Incr ;;
    Loop [
      Left;
      Right;
      Out
    ];;
    Done
  ).
Proof.
  reflexivity.
Qed.