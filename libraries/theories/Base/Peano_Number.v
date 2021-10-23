(** ペアノ式の自然数の型に関するモジュールです。 *)

Require Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を要求します。 *)

Import Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を開きます。 *)

Inductive T
  : Type
  := zero : T | succ : T -> T
.
(* from: originally defined by Hexirp *)

(** 主型です。 *)

Definition induction
    (P : T -> Type)
    (construct_zero : P zero)
    (construct_succ : forall x_p : T, P x_p -> P (succ x_p))
  : forall x : T, P x
  :=
    fix inductiver (x : T) {struct x} : P x
      :=
        match x with
            zero => construct_zero
          |
            succ x_p => construct_succ x_p (inductiver x_p)
        end
.
(* from: originally defined by Hexirp *)

(** 帰納法です。 *)

Definition recursion
    {P : Type}
    (construct_zero : P)
    (construct_succ : T -> P -> P)
  : T -> P
  := induction (fun x_ : T => P) construct_zero construct_succ
.
(* from: originally defined by Hexirp *)

(** 帰納法です。 *)
