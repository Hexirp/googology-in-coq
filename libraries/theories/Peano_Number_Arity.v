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

Inductive
  Peano_Number_Arity@{i s_i | i < s_i} (t : Peano_Number_Tag@{i}) : Type@{i}
    :=
      wrap
        :
            Universe.unwrap
              (
                Peano_Number_Tag.matching_nodep
                  Universe@{i s_i}
                  (Universe.wrap Peano_Number_Arity_Zero@{i})
                  (Universe.wrap Peano_Number_Arity_Successor@{i})
                  t
              )
          ->
            Peano_Number_Arity t
.
(* from: originally defined by Hexirp *)

(** 自然数の型のベータです。 *)

Definition
  unwrap@{i s_i | i < s_i} (t : Peano_Number_Tag@{i})
    :
        Peano_Number_Arity@{i s_i} t
      ->
        Universe.unwrap
          (
            Peano_Number_Tag.matching_nodep
              Universe@{i s_i}
              (Universe.wrap Peano_Number_Arity_Zero@{i})
              (Universe.wrap Peano_Number_Arity_Successor@{i})
              t
          )
    :=
      fun x : Peano_Number_Arity@{i s_i} t =>
        match x with wrap _ x_v => x_v end
.
(* from: originally defined by Hexirp *)

(** 自然数の型のベータです。 *)

Definition
  zero@{i s_i | i < s_i} (A : Type@{i})
    : Peano_Number_Arity@{i s_i} Peano_Number_Tag.zero -> A
    :=
      fun x : Peano_Number_Arity@{i s_i} Peano_Number_Tag.zero =>
        Peano_Number_Arity_Zero.matching_nodep A (unwrap x)
.
(* from: originally defined by Hexirp *)

(** 自然数の型のベータの [zero] です。 *)

Definition
  successor@{i s_i | i < s_i} (A : Type@{i}) (a : A)
    : Peano_Number_Arity@{i s_i} Peano_Number_Tag.successor -> A
    :=
      fun x : Peano_Number_Arity@{i s_i} Peano_Number_Tag.successor =>
        Peano_Number_Arity_Successor.matching_nodep A a (unwrap x)
.
(* from: originally defined by Hexirp *)

(** 自然数の型のベータの [successor] です。 *)
