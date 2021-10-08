From Coq Require Import List String Byte Ascii.
Import ListNotations.

Declare Scope bf.
Delimit Scope bf with bf.

(**
  Abstract Syntax of Brainfuck
*)
Inductive instruction : Type :=
  | Left
  | Right
  | Incr
  | Decr
  | In
  | Out
  | Loop : program -> instruction

with program : Type :=
  | Seq : instruction -> program -> program
  | Done : program.

(**
  Bind operator for optional types
*)
Definition bind {A B} (m : option A) (f : A -> option B) :=
  match m with
  | None => None
  | Some x => f x
  end.

Fixpoint parse_aux (n : nat) (s : string) (b : bool) {struct n} : option (program * string) :=
  match n with
  | 0 => None
  | S n =>
    match s%string with
    | String "+"%char next =>
      bind (parse_aux n next b) (fun '(p, next) => Some (Seq Incr p, next))
    | String "-"%char next =>
      bind (parse_aux n next b) (fun '(p, next) => Some (Seq Decr p, next))
    | String ">"%char next =>
      bind (parse_aux n next b) (fun '(p, next) => Some (Seq Right p, next))
    | String "<"%char next =>
      bind (parse_aux n next b) (fun '(p, next) => Some (Seq Left p, next))
    | String "."%char next =>
      bind (parse_aux n next b) (fun '(p, next) => Some (Seq Out p, next))
    | String ","%char next =>
      bind (parse_aux n next b) (fun '(p, next) => Some (Seq In p, next))
    | String "["%char next =>
      bind (parse_aux n next true) (fun '(p1, next1) =>
        bind (parse_aux n next1 b) (fun '(p2, next2) =>
          Some (Seq (Loop p1) Done, next2)
      ))
    | String "]"%char next =>
      if b then Some (Done, next) else None
    | String _ next =>
      bind (parse_aux n next b) (fun '(p, next) => Some (p, next))
    | EmptyString =>
      if b then None else Some (Done, EmptyString)
    end
  end.

(**
  Parse a string
*)
Definition parse_string (s : string) : option program :=
  match parse_aux (String.length s) s false with
  | Some (r, ""%string) => Some r
  | _ => None
  end.

(**
  Parse a list of bytes
*)
Definition parse_bytes (x : list byte) := bind (parse_string (string_of_list_byte x)) (fun x => Some x).

Fixpoint print_aux (n : nat) (x : program) :=
  match n with
  | O => None
  | S n => 
    match x with
    | Done => Some []
    | Seq Incr next =>
      bind (print_aux n next) (fun r => Some (byte_of_ascii ("+"%char)::r))
    | Seq Decr next =>
      bind (print_aux n next) (fun r => Some (byte_of_ascii ("-"%char)::r))
    | Seq Left next =>
      bind (print_aux n next) (fun r => Some (byte_of_ascii ("<"%char)::r))
    | Seq Right next =>
      bind (print_aux n next) (fun r => Some (byte_of_ascii (">"%char)::r))
    | Seq In next =>
      bind (print_aux n next) (fun r => Some (byte_of_ascii (","%char)::r))
    | Seq Out next =>
      bind (print_aux n next) (fun r => Some (byte_of_ascii ("."%char)::r))
    | Seq (Loop p) next =>
      bind (print_aux n next) (fun r =>
        bind (print_aux n p) (fun r' =>
          Some ([byte_of_ascii "["%char] ++ r' ++ [byte_of_ascii "]"%char] ++ r)
      ))
    end
  end.

(**
  Pretty print a program
*)
Definition print (p : program) := print_aux 512 p.

(* Registering the Brainfuck parser and pretty-printer *)
String Notation program parse_bytes print : bf.

(* List-like notation for syntax trees *)
Notation "[ x ; y ; .. ; z ]" := (Seq x (Seq y .. (Seq z Done) ..)) : bf.

Example test_parsing_and_printing :
  "++[<>.]"%bf = [
    Incr;
    Incr;
    Loop [
      Left;
      Right;
      Out
    ]
  ]%bf.
Proof.
  reflexivity.
Qed.