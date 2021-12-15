(** 直積型の道のモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Product.
Require Googology_In_Coq.Path.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Product (Product).
Import Googology_In_Coq.Path (Path, Path_Visible).

(** ライブラリを開きます。 *)

Definition
  Product_Path@{i | } (A : Type@{i}) (B : Type@{i})
    : Product A B -> Product A B -> Type@{i}
    := Path_Visible (Product A B)
.
(* from: originally defined by Hexirp *)

(** 直積型の道です。 *)

Definition
  iota_pair@{i | }
      {A : Type@{i}}
      {B : Type@{i}}
      (P : Product A B -> Type@{i})
      (constructor_pair : forall (x_1 : A) (x_2 : B), P (pair x_1 x_2))
      (x_1 : A)
      (x_2 : B)
    :
      Path
        (Product.matching P constructor_pair (pair x_1 x_2))
        (constructor_pair x_1 x_2)
    := Path.id
.
(* from: originally defined by Hexirp *)

(** 変換です。 *)

Definition
  coiota_first_nodep@{i | }
      {A : Type@{i}}
      {B : Type@{i}}
      {P : Type@{i}}
      (destructor_first : P -> A)
      (destructor_second : P -> B)
      (x : P)
    :
      Path
        (
          Product.first
            (Product.comatching destructor_first destructor_second x)
        )
        (destructor_first x)
    := Path.id
.
(* from: originally defined by Hexirp *)

(** 変換です。 *)

Definition
  coiota_second_nodep@{i | }
      {A : Type@{i}}
      {B : Type@{i}}
      {P : Type@{i}}
      (destructor_first : P -> A)
      (destructor_second : P -> B)
      (x : P)
    :
      Path
        (
          Product.second
            (Product.comatching destructor_first destructor_second x)
        )
        (destructor_second x)
    := Path.id
.
(* from: originally defined by Hexirp *)

(** 変換です。 *)
