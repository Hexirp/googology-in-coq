(** 依存関数の型に関するモジュールです。 *)

Require Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を要求します。 *)

Import Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を開きます。 *)

Definition T (A : Type) (B : A -> Type) : Type
  := forall a : A, B a
.
(* from: originally defined by Hexirp *)

(** 主型です。 *)

Definition apply {A : Type} {B : A -> Type}
  : (forall x : A, B x) -> forall x : A, B x
  := fun (f : forall x : A, B x) (x : A) => f x
.
(* from: originally defined by Hexirp *)

(** 関数の適用です。 *)
