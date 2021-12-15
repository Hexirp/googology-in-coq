(** 空型の道のモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Void.
Require Googology_In_Coq.Path.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Void (Void).
Import Googology_In_Coq.Path (Path, Path_Visible).

(** ライブラリを開きます。 *)

Definition
  Void_Path@{i | } : Void@{i} -> Void@{i} -> Type@{i} := Path_Visible Void@{i}
.
(* from: originally defined by Hexirp *)

(** 空型の道です。 *)
