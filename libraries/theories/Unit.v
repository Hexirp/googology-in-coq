(** 単一型に関するモジュールです。 *)

Require Googology_In_Coq.Base.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.

(** ライブラリを開きます。 *)

Inductive Unit@{i | } : Type@{i} := unit : Unit.
(* from: originally defined by Hexirp *)

(** 単一型です。 *)

Definition matching@{i | }
    (P : Unit@{i} -> Type@{i})
    (construct_unit : P unit)
  : forall x : Unit, P x
  := fun x : Unit => match x with unit => construct_unit end
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition matching_nodep@{i | } {P : Type@{i}} (construct_unit : P)
  : Unit@{i} -> P
  := matching (fun x_ => P) construct_unit
.
(* from: originally defined by Hexirp *)

(** 再帰です。 *)

Definition const@{i | } {A : Type@{i}} : A -> Unit@{i} := fun x : A => unit.
(* from: originally defined by Hexirp *)

(** 定数関数です。 *)
