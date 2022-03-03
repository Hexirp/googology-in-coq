(** 自然数の型に関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Sum.
Require Googology_In_Coq.Unit.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Sum (Sum).
Import Googology_In_Coq.Unit (Unit).

(** ライブラリを開きます。 *)

Definition Alpha@{i | } : Type@{i} := Sum@{i} Unit@{i} Unit@{i}.
(* from: originally defined by Hexirp *)

(** 自然数の型のアルファです。 *)

Definition zero@{i | } : Alpha@{i} := Sum.left Unit@{i} Unit@{i} Unit.unit.
(* from: originally defined by Hexirp *)

(** 自然数の型のアルファの第一構築子です。 *)

Definition succ@{i | } : Alpha@{i} := Sum.right Unit@{i} Unit@{i} Unit.unit.
(* from: originally defined by Hexirp *)

(** 自然数の型のアルファの第二構築子です。 *)

Definition
  matching@{i | }
      (P : Alpha@{i} -> Type@{i})
      (constructor_zero : P zero)
      (constructor_succ : P succ)
    : forall x : Alpha@{i}, P x
    :=
      Sum.matching
        Unit@{i}
        Unit@{i}
        P
        (
          Unit.matching
            (fun x_ : Unit => P (Sum.left Unit@{i} Unit@{i} x_))
            constructor_zero
        )
        (
          Unit.matching
            (fun x_ : Unit => P (Sum.right Unit@{i} Unit@{i} x_))
            constructor_succ
        )
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  matching_nodep@{i | }
      (P : Type@{i})
      (constructor_zero : P)
      (constructor_succ : P)
  : Alpha@{i} -> P
  := matching (fun x_ : Alpha@{i} => P) constructor_zero constructor_succ
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)
