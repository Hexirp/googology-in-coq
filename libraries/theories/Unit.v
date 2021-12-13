(** ユニットの型に関するモジュールです。 *)

Require Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を要求します。 *)

Import Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を開きます。 *)

Inductive T
  : Type
  := unit : T
.
(* from: originally defined by Hexirp *)

(** 主型です。 *)

Definition induction (P : T -> Type) (construct_unit : P unit)
  : forall x : T, P x
  := fun x : T => match x with unit => construct_unit end
.
(* from: originally defined by Hexirp *)

(** 帰納法です。 *)

Definition recursion {P : Type} (construct_unit : P)
  : T -> P
  := induction (fun x_ => P) construct_unit
.
(* from: originally defined by Hexirp *)

(** 再帰です。 *)

Definition const {A : Type}
  : A -> T
  := fun x : A => unit
.
(* from: originally defined by Hexirp *)

(** 定数関数です。 *)
