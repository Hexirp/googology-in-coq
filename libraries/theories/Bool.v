(** ブーリアン型に関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Function.
Require Googology_In_Coq.Sum.
Require Googology_In_Coq.Unit.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Function (Function).
Import Googology_In_Coq.Sum (Sum).
Import Googology_In_Coq.Unit (Unit).

(** ライブラリを開きます。 *)

Definition Bool@{i | } : Type@{i} := Sum@{i} Unit@{i} Unit@{i}.
(* from: originally defined by Hexirp *)

(** ブーリアン型です。 *)

Definition false@{i | } : Bool@{i} := Sum.left Unit@{i} Unit@{i} Unit.unit.
(* from: originally defined by Hexirp *)

(** ブーリアン型の第二構築子です。 *)

Definition true@{i | } : Bool@{i} := Sum.right Unit@{i} Unit@{i} Unit.unit.
(* from: originally defined by Hexirp *)

(** ブーリアン型の第一構築子です。 *)

Definition
  matching@{i | }
      (P : Bool@{i} -> Type@{i})
      (constructor_false : P false)
      (constructor_true : P true)
    : forall x : Bool@{i}, P x
    :=
      Sum.matching
        Unit@{i}
        Unit@{i}
        P
        (Unit.matching (fun x_ : Unit => P (Sum.left Unit@{i} Unit@{i} x_)) constructor_false)
        (Unit.matching (fun x_ : Unit => P (Sum.right Unit@{i} Unit@{i} x_)) constructor_true)
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  matching_nodep@{i | }
      {P : Type@{i}}
      (constructor_false : P)
      (constructor_true : P)
  : Bool@{i} -> P
  := matching (fun x_ : Bool@{i} => P) constructor_false constructor_true
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  matching_nodep_visible@{i | }
      (P : Type@{i})
      (constructor_false : P)
      (constructor_true : P)
  : Bool@{i} -> P
  := matching_nodep constructor_false constructor_true
.
(* from: originally defined by Hexirp *)

(** 引数が明示的な [matching_nodep] です。 *)

Definition
  and@{i | } : Bool@{i} -> Bool@{i} -> Bool@{i}
    := matching_nodep (Function.const false) Function.id
.
(* from: originally defined by Hexirp *)

(** 論理積です。 *)

Definition
  or@{i | } : Bool@{i} -> Bool@{i} -> Bool@{i}
    := matching_nodep (Function.id Bool@{i}) (Function.const Bool@{i} Bool@{i} true)
.
(* from: originally defined by Hexirp *)

(** 論理和です。 *)

Definition
  not@{i | } : Bool@{i} -> Bool@{i}
    := matching_nodep true false
.
(* from: originally defined by Hexirp *)

(** 否定です。 *)
