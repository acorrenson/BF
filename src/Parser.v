Require Import String Ascii List.
Import ListNotations.

(**
  Abstract syntax of the Brainfuck
  programing language
*)
Inductive instruction : Type :=
  | Incr
  | Decr
  | Left
  | Right
  | In
  | Out
  | Loop : list instruction -> instruction.

Definition bind {A B} (m : option A) (f : A -> option B) :=
  match m with
  | None => None
  | Some x => f x
  end.

Fixpoint parse_aux (n : nat) (s : string) (b : bool) {struct n} : option (list instruction * string) :=
  match n with
  | 0 => None
  | S n =>
    match s%string with
    | String "+"%char next =>
      bind (parse_aux n next b) (fun '(p, next) => Some (Incr :: p, next))
    | String "-"%char next =>
      bind (parse_aux n next b) (fun '(p, next) => Some (Decr :: p, next))
    | String ">"%char next =>
      bind (parse_aux n next b) (fun '(p, next) => Some (Right :: p, next))
    | String "<"%char next =>
      bind (parse_aux n next b) (fun '(p, next) => Some (Left :: p, next))
    | String "."%char next =>
      bind (parse_aux n next b) (fun '(p, next) => Some (Out :: p, next))
    | String ","%char next =>
      bind (parse_aux n next b) (fun '(p, next) => Some (In :: p, next))
    | String "["%char next =>
      bind (parse_aux n next true) (fun '(p1, next1) =>
        bind (parse_aux n next1 b) (fun '(p2, next2) =>
          Some ((Loop p1) :: p2, next2)
        )
      )
    | String "]"%char next =>
      if b then Some (nil, next) else None
    | String _ next =>
      bind (parse_aux n next b) (fun '(p, next) => Some (p, next))
    | EmptyString =>
      if b then None else Some (nil, EmptyString)
    end
  end.

Definition parse (s : string) : option (list instruction) :=
  match parse_aux (String.length s) s false with
  | Some (r, ""%string) => Some r
  | _ => None
  end.

Compute (parse "[++[><<]]"%string).


