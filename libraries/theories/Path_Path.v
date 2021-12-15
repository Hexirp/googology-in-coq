(** 道の道のモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Path.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Path (Path, Path_Visible).

(** ライブラリを開きます。 *)

Definition
  Path_Path@{i | } {A : Type@{i}} (x_L : A) (x_R : A)
    : Path x_L x_R -> Path x_L x_R -> Type@{i}
    := Path_Visible (Path x_L x_R)
.
(* from: originally defined by Hexirp *)

(** 道の道です。 *)
