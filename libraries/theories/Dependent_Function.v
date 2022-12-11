(** 依存関数型のモジュールです。 *)

Require Googology_In_Coq.Base.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.

(** ライブラリを開きます。 *)

Definition Dependent_Function@{ i | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) : Type@{ i } := forall x : A, B x.
(* from: originally defined by Hexirp *)

(** 依存関数型です。 *)

Definition map_Dependent_Function@{ i | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( C : Type@{ i } ) ( D : C -> Type@{ i } ) ( f : C -> A ) ( g : forall x : C, B ( f x ) -> D x ) ( x : Dependent_Function A B ) : Dependent_Function C D := fun y : C => g y ( x ( f y ) ).
(* from: originally defined by Hexirp *)

(** 依存関数型から依存関数への写像です。 *)
