(** ウ型の道のモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Function.
Require Googology_In_Coq.Dependent_Sum.
Require Googology_In_Coq.W_type.
Require Googology_In_Coq.Path.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Function (Function).
Import Googology_In_Coq.Dependent_Sum (Dependent_Sum).
Import Googology_In_Coq.W_type (W_type).
Import Googology_In_Coq.Path (Path, Path_Visible).

(** ライブラリを開きます。 *)

Definition
  W_type_Path@{i | } (A : Type@{i}) (B : A -> Type@{i})
    : W_type A B -> W_type A B -> Type@{i}
    := Path_Visible (W_type A B)
.
(* from: originally defined by Hexirp *)

(** ウ型の道です。 *)

Definition
  iota_sup@{i | }
      {A : Type@{i}}
      {B : A -> Type@{i}}
      (
        constructor_sup
          :
            forall
              x_v : Dependent_Sum A (fun a : A => Function (B a) (W_type A B))
            ,
              P (W_type.sup x_v)
      )
      (x_v : Dependent_Sum A (fun a : A => Function (B a) (W_type A B)))
    :
      Path
        (W_type.matching P constructor_sup x_v)
        (constructor_sup x_v)
    := Path.id
.
(* from: originally defined by Hexirp *)

(** 変換です。 *)
