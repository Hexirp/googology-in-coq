(** 依存直積型についてのモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Dependent_Function.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Dependent_Function (Dependent_Function).

(** ライブラリを開きます。 *)

Definition Dependent_Product@{i | } (A : Type@{i}) (B : A -> Type@{i})
  : Type@{i}
  := Dependent_Function A B
.
(* from: originally defined by Hexirp *)

(** 主型です。 *)
