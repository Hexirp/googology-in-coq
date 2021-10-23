(** ブール型に関するモジュールです。 *)

Require Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を要求します。 *)

Import Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を開きます。 *)

Inductive T
  : Type
  := true : T | false : T
.
(* from: originally defined by Hexirp *)

(** 主型です。 *)

Definition induction
    (P : T -> Type)
    (construct_true : P true)
    (construct_false : P false)
  : forall x : T, P x
  :=
    fun x : T =>
      match x with
          true => construct_true
        |
          false => construct_false
      end
.
(* from: originally defined by Hexirp *)

(** 帰納法です。 *)

Definition recursion
    {P : Type}
    (construct_true : P)
    (construct_false : P)
  : T -> P
  := induction (fun x_ : T => P) construct_true construct_false
.
(* from: originally defined by Hexirp *)

(** 再帰です。 *)
