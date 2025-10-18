(** 単一型に関するモジュールです。 *)

Require Googology_In_Coq.Base.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.

(** ライブラリを開きます。 *)

Inductive Unit@{i | } : Type@{i} := unit : Unit.
(* from: originally defined by Hexirp *)

(** 単一型です。 *)

Definition
  matching@{i | } (P : Unit@{i} -> Type@{i}) (constructor_unit : P unit)
    : forall x : Unit, P x
    :=
      fun x : Unit =>
        match x as x_ return P x_ with unit => constructor_unit end
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  matching_nodep@{i | } (P : Type@{i}) (constructor_unit : P) : Unit@{i} -> P
    := matching (fun x_ => P) constructor_unit
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  comatching_nodep@{i | } (P : Type@{i}) : P -> Unit@{i} := fun x : P => unit
.
(* from: originally defined by Hexirp *)

(** 余場合分けです。 *)

Definition const@{i | } (A : Type@{i}) : A -> Unit@{i} := fun x : A => unit.
(* from: originally defined by Hexirp *)

(** 定数関数です。 *)
