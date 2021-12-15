(** 依存関数型の道のモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Dependent_Function.
Require Googology_In_Coq.Path.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Dependent_Function (Dependent_Function).
Import Googology_In_Coq.Path (Path, Path_Visible).

(** ライブラリを開きます。 *)

Definition
  Dependent_Function_Path@{i | } (A : Type@{i}) (B : A -> Type@{i})
    : Dependent_Function A B -> Dependent_Function A B -> Type@{i}
    := Path_Visible (Dependent_Function A B)
.

(** 依存関数型の道です。 *)
