(** 自然数の型に関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Function.
Require Googology_In_Coq.Dependent_Sum.
Require Googology_In_Coq.Sum.
Require Googology_In_Coq.Void.
Require Googology_In_Coq.Unit.
Require Googology_In_Coq.W_type.
Require Googology_In_Coq.Bool.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Function (Function).
Import Googology_In_Coq.Dependent_Sum (Dependent_Sum).
Import Googology_In_Coq.Sum (Sum).
Import Googology_In_Coq.Void (Void).
Import Googology_In_Coq.Unit (Unit).
Import Googology_In_Coq.W_type (W_type).
Import Googology_In_Coq.Bool (Bool).

(** ライブラリを開きます。 *)

Definition
  Peano_Number@{i s_i | i < s_i} : Type@{i}
    :=
      W_type@{i}
        Bool@{i}
        (Bool.matching_nodep_visible@{s_i} Type@{i} Void@{i} Unit@{i})
.
(* from: originally defined by Hexirp *)

(** 自然数の型です。 *)

Definition
  zero@{i s_i | i < s_i} : Peano_Number@{i s_i}
    := W_type.sup (Dependent_Sum.pair Bool.false Void.matching_nodep)
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
