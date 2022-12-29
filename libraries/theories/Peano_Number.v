(** 自然数型に関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Path.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Path.

(** ライブラリを開きます。 *)

Inductive Peano_Number@{ i | } : Type@{ i } := zero_Peano_Number : Peano_Number | succ_Peano_Number : Peano_Number -> Peano_Number.
(* from: originally defined by Hexirp *)

(** 自然数型です。 *)
