(** 依存直積型の道のモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Dependent_Product.
Require Googology_In_Coq.Path.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Dependent_Product (Dependent_Product).
Import Googology_In_Coq.Path (Path, Path_Visible).

(** ライブラリを開きます。 *)

Definition
  Dependent_Product_Path@{i | } (A : Type@{i}) (B : Type@{i})
    : Dependent_Product_Path A B -> Dependent_Product_Path A B -> Type@{i}
    := Path_Visible (Dependent_Product_Path A B)
.
(* from: originally defined by Hexirp *)

(** 依存直積型の道です。 *)
