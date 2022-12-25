(** 依存直積型についてのモジュールです。 *)

Require Googology_In_Coq.Base.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.

(** ライブラリを開きます。 *)

Definition Dependent_Product@{ i | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) : Type@{ i } := forall x : A, B x.
(* from: originally defined by Hexirp *)

(** 依存直積型です。 *)

Definition map@{ i j k l | } ( A : Type@{ i } ) ( B : A -> Type@{ j } ) ( C : Type@{ k } ) ( D : C -> Type@{ l } ) ( f : C -> A ) ( g : forall x : C, B ( f x ) -> D x ) ( x : forall a : A, B a ) : forall c : C, D c := fun y : C => g y ( x ( f y ) ).
(* from: originally defined by Hexirp *)

(** 依存直積型の写像です。 *)
