(** 自然数の型に関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Function.
Require Googology_In_Coq.Dependent_Sum.
Require Googology_In_Coq.Sum.
Require Googology_In_Coq.Void.
Require Googology_In_Coq.Unit.
Require Googology_In_Coq.W_type.
Require Googology_In_Coq.Universe.
Require Googology_In_Coq.Bool.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Function (Function).
Import Googology_In_Coq.Dependent_Sum (Dependent_Sum).
Import Googology_In_Coq.Sum (Sum).
Import Googology_In_Coq.Void (Void).
Import Googology_In_Coq.Unit (Unit).
Import Googology_In_Coq.W_type (W_type).
Import Googology_In_Coq.Universe (Universe).
Import Googology_In_Coq.Bool (Bool).

(** ライブラリを開きます。 *)

Definition Alpha@{i | } : Type@{i} := Sum@{i} Unit@{i} Unit@{i}.
(* from: originally defined by Hexirp *)

(** 自然数の型のアルファです。 *)

Definition
  Beta@{i s_i | i < s_i} : Alpha@{i} -> Type@{i}
    :=
      Sum.matching_nodep@{s_i}
        Unit@{i}
        Unit@{i}
        Universe@{i s_i}
        (Unit.matching_nodep@{s_i} Universe@{i s_i} Void@{i})
        (Unit.matching_nodep@{s_i} Universe@{i s_i} Unit@{i})
.
(* from: originally defined by Hexirp *)

(** 自然数の型のベータです。 *)

Definition
  Peano_Number@{i s_i | i < s_i} : Type@{i}
    := W_type@{i} Alpha@{i} Beta@{i s_i}
.
(* from: originally defined by Hexirp *)

(** 自然数の型です。 *)

Definition
  zero@{i s_i | i < s_i} : Peano_Number@{i s_i}
    :=
      W_type.sup
        Alpha@{i}
        Beta@{i s_i}
        (
          W_type.Alpha.pair
            W_type.Beta.Beta@{i}
            W_type@{i}
            Alpha@{i}
            Beta@{i s_i}
            (Sum.left Unit@{i} Unit@{i} Unit.unit)
            (Void.matching_nodep (W_type Alpha@{i} Beta@{i s_i}))
        )
.
(* from: originally defined by Hexirp *)

(** 自然数の型の第一構築子です。 *)

Definition
  succ@{i s_i | i < s_i} (n_p : Peano_Number@{i s_i}) : Peano_Number@{i s_i}
    := W_type.sup (Dependent_Sum.pair Bool.true (Unit.matching_nodep n_p))
.
(* from: originally defined by Hexirp *)

(** 自然数の型の第二構築子です。 *)

Definition
  matching@{i s_i | i < s_i}
      (P : Peano_Number@{i s_i} -> Type@{i})
      (constructor_zero : P zero@{i s_i})
      (
        constructor_succ
          : forall x_p : Peano_Number@{i s_i}, P (succ@{i s_i} x_p)
      )
    : forall x : Peano_Number@{i s_i}, P x
.
Proof.
  refine (W_type.matching P _).
  refine (Dependent_Sum.matching _ _).
  refine (Bool.matching _ _ _).
  exact _.
Defined.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  induction@{i s_i | i < s_i}
      (P : Peano_Number@{i s_i} -> Type@{i})
      (constructor_zero : P zero@{i s_i})
      (
        constructor_succ
          : forall x_p : Peano_Number@{i s_i}, P x_p -> P (succ@{i s_i} x_p)
      )
    : forall x : Peano_Number@{i s_i}, P x
    := _
.
(* from: originally defined by Hexirp *)

(** 帰納法の原理です。 *)
