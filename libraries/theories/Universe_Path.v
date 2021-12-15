(** 超型の道のモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Universe.
Require Googology_In_Coq.Path.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Universe (Universe).
Import Googology_In_Coq.Path (Path, Path_Visible).

(** ライブラリを開きます。 *)

Definition
  Universe_Path@{i s_i | i < s_i} : Universe@{i} -> Universe@{i} -> Type@{s_i}
    := Path_Visible@{s_i} Universe@{i}
.
(* from: originally defined by Hexirp *)

(** 超型の道です。 *)
