(** 依存直和型の道のモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Dependent_Sum.
Require Googology_In_Coq.Path.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Dependent_Sum (Dependent_Sum).
Import Googology_In_Coq.Path (Path, Path_Visible).

(** ライブラリを開きます。 *)

Definition
  Dependent_Sum_Path@{i | } (A : Type@{i}) (B : A -> Type@{i})
    : Dependent_Sum A B -> Dependent_Sum A B -> Type@{i}
    := Path_Visible (Dependent_Sum A B)
.
(* from: originally defined by Hexirp *)

(** 関数型の道です。 *)

Definition
  iota_pair@{i | }
      {A : Type@{i}}
      {B : A -> Type@{i}}
      (P : Dependent_Sum A B -> Type@{i})
      (constructor_pair : forall (a : A) (b : B a), P (Dependent_Sum.pair a b))
      (a : A)
      (b : B a)
    :
      Path
        (Dependent_Sum.matching P constructor_pair (Dependent_Sum.pair a b))
        (constructor_pair a b)
    := Path.id
.
(* from: originally defined by Hexirp *)

(** 変換です。 *)
