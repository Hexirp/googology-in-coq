(** ブーリアン型に関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Sum.
Require Googology_In_Coq.Unit.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Sum (Sum).
Import Googology_In_Coq.Unit (Unit).

(** ライブラリを開きます。 *)

Definition Bool@{i | } : Type@{i} := Sum@{i} Unit@{i} Unit@{i}.
(* from: originally defined by Hexirp *)

(** ブーリアン型です。 *)

Definition true@{i | } : Bool@{i} := Sum.left Unit.unit.
(* from: originally defined by Hexirp *)

(** ブーリアン型の第一構築子です。 *)

Definition false@{i | } : Bool@{i} := Sum.right Unit.unit.
(* from: originally defined by Hexirp *)

(** ブーリアン型の第二構築子です。 *)

Definition
  matching@{i | }
      (P : Bool@{i} -> Type@{i})
      (constructor_true : P true)
      (constructor_false : P false)
    : forall x : Bool@{i}, P x
    :=
      Sum.matching
        P
        (Unit.matching (fun x_ : Unit => P (Sum.left x_)) constructor_true)
        (Unit.matching (fun x_ : Unit => P (Sum.right x_)) constructor_false)
.
(* from: originally defined by Hexirp *)

(** 帰納法の原理です。 *)

Definition
  matching_nodep
      {P : Type@{i}}
      (constructor_true : P)
      (constructor_false : P)
  : Bool@{i} -> P
  := matching (fun x_ : Bool@{i} => P) constructor_true constructor_false
.
(* from: originally defined by Hexirp *)

(** 再帰です。 *)
