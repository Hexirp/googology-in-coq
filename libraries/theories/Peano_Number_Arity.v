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
  Peano_Number_Arity@{i s_i | i < s_i} (x : Peano_Number_Tag@{i}) : Type@{i}
    :=
      wrap
        :
            Universe.unwrap
              (
                Peano_Number_Tag.matching_nodep
                  Universe@{i s_i}
                  (Universe.wrap Peano_Number_Arity_Zero@{i})
                  (Universe.wrap Peano_Number_Arity_Successor@{i})
                  x
              )
          ->
            Peano_Number_Arity
.
(* from: originally defined by Hexirp *)

(** 自然数の型のベータです。 *)

Inductive
  unwrap@{i s_i | i < s_i} (x : Peano_Number_Tag@{i})
    :
        Peano_Number_Arity@{i s_i}
      ->
        Universe.unwrap
          (
            Peano_Number_Tag.matching_nodep
              Universe@{i s_i}
              (Universe.wrap Peano_Number_Arity_Zero@{i})
              (Universe.wrap Peano_Number_Arity_Successor@{i})
              x
          )
    :=
      fun x : Peano_Number_Arity@{i s_i} =>
        match x with wrap _ x_v => x_v end
.
(* from: originally defined by Hexirp *)

(** 自然数の型のベータです。 *)

Definition
  zero@{i s_i | i < s_i} (A : Type@{i})
    : Peano_Number_Arity@{i s_i} Peano_Number_Tag.zero -> A
    := Peano_Number_Arity_Zero.matching_nodep A
.
(* from: originally defined by Hexirp *)

(** 自然数の型のベータの [zero] です。 *)

Definition
  successor@{i s_i | i < s_i} (A : Type@{i}) (x_p : A)
    : Peano_Number_Arity@{i s_i} Peano_Number_Tag.successor -> A
    := Peano_Number_Arity_Successor.matching_nodep A x_p
.
(* from: originally defined by Hexirp *)

(** 自然数の型のベータの [successor] です。 *)
