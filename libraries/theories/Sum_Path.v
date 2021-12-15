(** 直和型の道のモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Sum.
Require Googology_In_Coq.Path.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Sum (Sum).
Import Googology_In_Coq.Path (Path, Path_Visible).

(** ライブラリを開きます。 *)

Definition
  Sum_Path@{i | } (A : Type@{i}) (B : Type@{i})
    : Sum A B -> Sum A B -> Type@{i}
    := Path_Visible (Sum A B)
.
(* from: originally defined by Hexirp *)

(** 直和型の道です。 *)

Definition
  iota_left@{i | }
      {A : Type@{i}}
      {B : Type@{i}}
      (P : Sum A B -> Type@{i})
      (constructor_left : forall x_L : A, P (Sum.left x_L))
      (constructor_right : forall x_R : B, P (Sum.right x_R))
      (x_L : A)
    :
      Path
        (Sum.matching P constructor_left constructor_right (Sum.left x_L))
        (constructor_left x_L)
    := Path.id
.
(* from: originally defined by Hexirp *)

(** 変換です。 *)

Definition
  iota_right@{i | }
      {A : Type@{i}}
      {B : Type@{i}}
      (P : Sum A B -> Type@{i})
      (constructor_left : forall x_L : A, P (Sum.left x_L))
      (constructor_right : forall x_R : B, P (Sum.right x_R))
      (x_R : B)
    :
      Path
        (Sum.matching P constructor_left constructor_right (Sum.right x_R))
        (constructor_right x_R)
    := Path.id
.
(* from: originally defined by Hexirp *)

(** 変換です。 *)
