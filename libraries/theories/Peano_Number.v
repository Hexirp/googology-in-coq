(** 自然数の型に関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Function.
Require Googology_In_Coq.Sum.
Require Googology_In_Coq.Void.
Require Googology_In_Coq.Unit.
Require Googology_In_Coq.W_type.
Require Googology_In_Coq.Bool.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Function (Function).
Import Googology_In_Coq.Sum (Sum).
Import Googology_In_Coq.Void (Void).
Import Googology_In_Coq.Unit (Unit).
Import Googology_In_Coq.W_type (W_type)
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
