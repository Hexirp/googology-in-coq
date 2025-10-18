(** 依存直積型についてのモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Path.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Path.

(** ライブラリを開きます。 *)

Definition Dependent_Product@{ i | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) : Type@{ i } := forall a : A, B a.
(* from: originally defined by Hexirp *)

(** 依存直積型です。 *)

Definition comatching_Dependent_Product@{ i | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( P : Type@{ i } ) ( d : forall ( a : A ), P -> B a ) ( x : P ) : Dependent_Product A B := fun a : A => d a x.
(* from: originally defined by Hexirp *)

(** 依存直積型の余場合分けです。 *)

Definition identity_comatching_Dependent_Product@{ i | } ( functional_extensionality : forall ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( f : forall a : A, B a ) ( g : forall a : A, B a ), ( forall a : A, Path ( B a ) ( f a ) ( g a ) ) -> Path ( forall a : A, B a ) f g ) ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( P : Type@{ i } ) ( codisplay : Dependent_Product A B -> P ) ( d : forall ( a : A ), P -> B a ) ( id : forall ( a : A ) ( x : Dependent_Product A B ), Path ( B a ) ( d a ( codisplay x ) ) ( x a ) ) ( x : Dependent_Product A B ) : Path ( Dependent_Product A B ) ( comatching_Dependent_Product A B P d ( codisplay x ) ) x.
Proof.
  refine ( functional_extensionality A B ( comatching_Dependent_Product A B P d ( codisplay x ) ) x _ ).
  refine ( fun a : A => _ ).
  change ( Path ( B a ) ( comatching_Dependent_Product A B P d ( codisplay x ) a ) ( x a ) ).
  change ( Path ( B a ) ( d a ( codisplay x ) ) ( x a ) ).
  exact ( id a x ).
Defined.
(* from: originally defined by Hexirp *)

(** 依存直積型の余場合分けの恒等式です。 *)

Definition map@{ i j k l | } ( A : Type@{ i } ) ( B : A -> Type@{ j } ) ( C : Type@{ k } ) ( D : C -> Type@{ l } ) ( f : C -> A ) ( g : forall x : C, B ( f x ) -> D x ) ( x : forall a : A, B a ) : forall c : C, D c := fun y : C => g y ( x ( f y ) ).
(* from: originally defined by Hexirp *)

(** 依存直積型の写像です。 *)
