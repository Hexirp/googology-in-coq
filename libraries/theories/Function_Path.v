(** 関数型の道のモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Function.
Require Googology_In_Coq.Path.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Function (Function).
Import Googology_In_Coq.Path (Path, Path_Visible).

(** ライブラリを開きます。 *)

Definition
  Function_Path@{i | } (A : Type@{i}) (B : Type@{i})
    : Function A B -> Function A B -> Type@{i}
    := Path_Visible (Function A B)
.
(* from: originally defined by Hexirp *)

(** 関数型の道です。 *)
