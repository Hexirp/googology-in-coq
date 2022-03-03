(** 自然数の型のベータに関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Universe.
Require Googology_In_Coq.Peano_Number_Alpha.
Require Googology_In_Coq.Peano_Number_Beta_Zero.
Require Googology_In_Coq.Peano_Number_Beta_Succ.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Universe (Universe).
Import Googology_In_Coq.Peano_Number_Alpha (Alpha).
Import Googology_In_Coq.Peano_Number_Beta_Zero (Zero).
Import Googology_In_Coq.Peano_Number_Beta_Succ (Succ).

(** ライブラリを開きます。 *)

Definition
  Beta@{i s_i | i < s_i} : Alpha@{i} -> Type@{i}
    := Alpha.matching_nodep Universe@{i s_i} Zero@{i} Succ@{i}
.
(* from: originally defined by Hexirp *)

(** 自然数の型のベータです。 *)

Definition
  zero@{i s_i | i < s_i} (A : Type@{i}) : Beta Alpha.zero -> A
    := Zero.matching_nodep A
.
(* from: originally defined by Hexirp *)

(** 自然数の型のベータの [zero] です。 *)

Definition
  succ@{i s_i | i < s_i} (A : Type@{i}) (x_p : A) : Beta Alpha.succ -> A
    := Succ.matching_nodep A x_p
.
(* from: originally defined by Hexirp *)

(** 自然数の型のベータの [succ] です。 *)
