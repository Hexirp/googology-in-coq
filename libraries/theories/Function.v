(** 関数型に関するモジュールです。 *)

Require Googology_In_Coq.Base.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.

(** ライブラリを開きます。 *)

Definition Function@{ i | } ( A : Type@{ i } ) ( B : Type@{ i } ) : Type@{ i } := A -> B.
(* from: originally defined by Hexirp *)

(** 関数型です。 *)

Definition id_Function@{ i | } ( A : Type@{ i } ) : Function@{ i } A A := fun x : A => x.
(* from: originally defined by Hexirp *)

(** 恒等関数です。 *)

Definition const_Function@{ i | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( x : A ) : Function@{ i } B A := fun y : B => x.
(* from: originally defined by Hexirp *)

(** 定数関数です。 *)

Definition comp_Function@{ i | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( C : Type@{ i } ) ( f : Function@{ i } B C ) ( g : Function@{ i } A B ) : Function@{ i } A C := fun x : A => f ( g x ).
(* from: originally defined by Hexirp *)

(** 関数の合成です。 *)

Definition map@{ i | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( C : Type@{ i } ) ( D : Type@{ i } ) ( f : C -> A ) ( g : B -> D ) ( x : Function@{ i } A B ) : Function@{ i } C D := fun y : C => g ( x ( f y ) ).
(* from: originally defined by Hexirp *)

(** 関数型から関数型への写像です。 *)
