(** 型の型です。 *)

Require Googology_In_Coq.Base.Base.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を開きます。 *)

Definition of {A : Type}
  : A -> Type
  := fun x : A => A
.
(* from: originally defined by Hexirp *)

(** 値の型です。 *)
