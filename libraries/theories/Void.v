(** 空型に関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Path.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Path.

(** ライブラリを開きます。 *)

Inductive Void@{ i | } : Type@{ i } :=.
(* from: originally defined by Hexirp *)

(** 空型です。 *)

Definition matching_Void@{ i j | } ( P : Type@{ j } ) ( x : Void@{ i } ) : P := match x with end.
(* from: originally defined by Hexirp *)

(** 空型の場合分けです。 *)

Definition identity_matching_Void@{ i j | } ( P : Type@{ j } ) ( display : P -> Void@{ i } ) ( x : Void@{ i } ) : Path Void@{ i } ( display ( matching_Void P x ) ) x := match x as x_ return Path Void@{ i } ( display ( matching_Void P x_ ) ) x_ with end.
(* from: originally defined by Hexirp *)

(** 空型の場合分けです。 *)

Definition dependent_matching_Void@{ i j | } ( P : Void@{ i } -> Type@{ j } ) ( x : Void ) : P x := match x as x_ return P x_ with end.
(* from: originally defined by Hexirp *)

(** 空型の依存場合分けです。 *)

Definition absurd@{ i j | } ( A : Type@{ i } ) : Void@{ j } -> A := matching_Void A.
(* from: originally defined by Hexirp *)

(** 空型から任意の型を取り出す関数です。 *)
