(** ボトムの型に関するモジュールです。 *)

Require Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を要求します。 *)

Import Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を開きます。 *)

Inductive T
  : Type
  :=
.
(* from: originally defined by Hexirp *)

(** 主型です。 *)

Definition induction (P : T -> Type)
  : forall x : T, P x
  := fun x : T => match x with end
.
(* from: originally defined by Hexirp *)

(** 帰納法です。 *)

Definition recursion {P : Type}
  : T -> P
  := induction (fun x_ : T => P)
.
(* from: originally defined by Hexirp *)

(** 帰納法です。 *)

Definition absurd {A : Type}
  : T -> A
  := recursion
.
(* from: originally defined by Hexirp *)

(** 矛盾による証明です。 *)
