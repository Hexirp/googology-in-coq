(** 依存積の型についてのモジュールです。 *)

Require Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を要求します。 *)

Import Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を開きます。 *)

Definition T (A : Type) (B : A -> Type) : Type
  := forall a : A, B a
.
(* from: originally defined by Hexirp *)

(** 主型です。 *)
