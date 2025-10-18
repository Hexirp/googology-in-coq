(** 関数型に関するモジュールです。 *)

Require Googology_In_Coq.Base.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.

(** ライブラリを開きます。 *)

Definition Function@{ i | } ( A : Type@{ i } ) ( B : Type@{ i } ) : Type@{ i } := A -> B.
(* from: originally defined by Hexirp *)

(** 関数型です。 *)

Definition id_Function@{ i | } ( A : Type@{ i } ) : A -> A := fun x : A => x.
(* from: originally defined by Hexirp *)

(** 恒等関数です。 *)

Definition const_Function@{ i j | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( x : A ) : B -> A := fun y : B => x.
(* from: originally defined by Hexirp *)

(** 定数関数です。 *)

Definition comp_Function@{ i j k | } ( A : Type@{ i } ) ( B : Type@{ j } ) ( C : Type@{ k } ) ( f : B -> C ) ( g : A -> B ) : A -> C := fun x : A => f ( g x ).
(* from: originally defined by Hexirp *)

(** 関数の合成です。 *)

Definition map@{ i j k l | } ( A : Type@{ i } ) ( B : Type@{ j } ) ( C : Type@{ k } ) ( D : Type@{ l } ) ( f : C -> A ) ( g : B -> D ) ( x : A -> B ) : C -> D := fun y : C => g ( x ( f y ) ).
(* from: originally defined by Hexirp *)

(** 関数型から関数型への写像です。 *)
