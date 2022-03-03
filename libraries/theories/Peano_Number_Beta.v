(** 自然数の型のベータに関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Universe.
Require Googology_In_Coq.Peano_Number.Alpha.
Require Googology_In_Coq.Peano_Number.Beta.Zero.
Require Googology_In_Coq.Peano_Number.Beta.Succ.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Universe (Universe).
Import Googology_In_Coq.Peano_Number.Alpha (Alpha).

(** ライブラリを開きます。 *)

Definition Zero@{i | } : Type@{i} := Zero.Zero@{i}.
(* from: originally defined by Hexirp *)

(** 自然数の型のベータの [zero] です。 *)

Definition Succ@{i | } : Type@{i} := Succ.Succ@{i}.
(* from: originally defined by Hexirp *)

(** 自然数の型のベータの [succ] です。 *)

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
