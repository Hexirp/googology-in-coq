(** 自然数の型のベータの [succ] に関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Unit.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Unit (Unit).

(** ライブラリを開きます。 *)

Definition Succ@{i | } : Type@{i} := Unit@{i}.
(* from: originally defined by Hexirp *)

(** 自然数の型のベータの [succ] です。 *)

Definition unit@{i | } : Unit@{i} := Unit.unit.
(* from: originally defined by Hexirp *)

(** 自然数の型のベータの [succ] の構築子です。 *)

Definition
  matching@{i | } (P : Succ@{i} -> Type@{i}) (constructor_unit : P unit)
    : forall x : Succ@{i}, P x
    := Unit.matching P constructor_unit
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  matching_nodep@{i | } (P : Type@{i}) (constructor_unit : P) : Succ@{i} -> P
    := matching (fun x_ : Succ@{i} => P) constructor_unit
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  comatching_nodep@{i | } (P : Type@{i}) : P -> Succ@{i} := fun x : P => unit
.
(* from: originally defined by Hexirp *)

(** 余場合分けです。 *)
