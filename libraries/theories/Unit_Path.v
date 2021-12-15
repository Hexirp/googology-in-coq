(** 単一型の道のモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Unit.
Require Googology_In_Coq.Path.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Unit (Unit).
Import Googology_In_Coq.Path (Path, Path_Visible).

(** ライブラリを開きます。 *)

Definition
  Unit_Path@{i | } : Unit@{i} -> Unit@{i} -> Type@{i} := Path_Visible Unit@{i}
.
(* from: originally defined by Hexirp *)

(** 単一型の道です。 *)

Definition
  iota_unit@{i | } 
      (P : Unit@{i} -> Type@{i})
      (constructor_unit : P Unit.unit)
    :
      Path
        (Unit.matching P constructor_unit Unit.unit)
        constructor_unit
    := Path.id
.
(* from: originally defined by Hexirp *)

(** 変換です。 *)

Definition
  coiota_unit@{i | } (P : Type@{i}) (x : P)
    : Path (Unit.comatching_nodep x) Unit.unit
    := Path.id
.
(* from: originally defined by Hexirp *)

(** 変換です。 *)
