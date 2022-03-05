(** 自然数の型のベータに関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Universe.
Require Googology_In_Coq.Peano_Number_Tag.
Require Googology_In_Coq.Peano_Number_Arity_Zero.
Require Googology_In_Coq.Peano_Number_Arity_Successor.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Universe (Universe).
Import Googology_In_Coq.Peano_Number_Tag (Peano_Number_Tag).
Import Googology_In_Coq.Peano_Number_Arity_Zero (Peano_Number_Arity_Zero).
Import Googology_In_Coq.Peano_Number_Arity_Successor (Peano_Number_Arity_Successor).

(** ライブラリを開きます。 *)

Definition
  Peano_Number_Arity@{i s_i | i < s_i} : Peano_Number_Tag@{i} -> Type@{i}
    := Peano_Number_Tag.matching_nodep Universe@{i s_i} Peano_Number_Arity_Zero@{i} Peano_Number_Arity_Successor@{i}
.
(* from: originally defined by Hexirp *)

(** 自然数の型のベータです。 *)

Definition
  zero@{i s_i | i < s_i} (A : Type@{i}) : Peano_Number_Arity Peano_Number_Tag.zero -> A
    := Peano_Number_Arity_Zero.matching_nodep A
.
(* from: originally defined by Hexirp *)

(** 自然数の型のベータの [zero] です。 *)

Definition
  succ@{i s_i | i < s_i} (A : Type@{i}) (x_p : A) : Peano_Number_Arity Peano_Number_Tag.succ -> A
    := Peano_Number_Arity_Successor.matching_nodep A x_p
.
(* from: originally defined by Hexirp *)

(** 自然数の型のベータの [succ] です。 *)
