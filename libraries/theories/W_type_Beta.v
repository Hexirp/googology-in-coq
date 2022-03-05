(** ウ型のベータに関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Function.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Function (Function).

(** ライブラリを開きます。 *)

Definition
  W_type_Beta@{i | }
      (t : forall A : Type@{i}, (A -> Type@{i}) -> Type@{i})
      (A : Type@{i})
      (B : A -> Type@{i})
    : A -> Type@{i}
    := fun a : A => Function (B a) (t A B)
.
(* from: originally defined by Hexirp *)

(** ウ型のベータです。 *)

Definition
  apply@{i | }
      (t : forall A : Type@{i}, (A -> Type@{i}) -> Type@{i})
      (A : Type@{i})
      (B : A -> Type@{i})
      (a : A)
    : W_type_Beta t A B a -> B a -> t A B
    := Function.apply (B a) (t A B)
.
(* from: originally defined by Hexirp *)

(** ウ型のベータの適用です。 *)
