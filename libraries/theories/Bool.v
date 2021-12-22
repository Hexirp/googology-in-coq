(** ブール型に関するモジュールです。 *)

Require Googology_In_Coq.Base.Base.
Require Googology_In_Coq.Base.Unit.
Require Googology_In_Coq.Base.Sum.

(** [Googology_In_Coq.Base.Base] を要求します。 *)

Import Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を開きます。 *)

Definition T : Type := Sum.T Unit.T Unit.T.
(* from: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html *)

(** 主型です。 *)

Definition true : T := Sum.left Unit.unit.
(* from: originally defined by Hexirp *)

(** 一つ目の構築子です。 *)

Definition false : T := Sum.right Unit.unit.
(* from: originally defined by Hexirp *)

(** 二つ目の構築子です。 *)

Definition induction
    (P : T -> Type)
    (construct_true : P true)
    (construct_false : P false)
  : forall x : T, P x
  :=
    Sum.induction
      P
      (Unit.induction (fun x_ : Unit.T => P (Sum.left x_)) construct_true)
      (Unit.induction (fun x_ : Unit.T => P (Sum.right x_)) construct_false)
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
