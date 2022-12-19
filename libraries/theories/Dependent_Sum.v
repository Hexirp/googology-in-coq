(** 依存直和型に関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Path.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Path.

(** ライブラリを開きます。 *)

Inductive Dependent_Sum@{ i | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) : Type@{ i } := pair_Dependent_Sum : forall a : A, B a -> Dependent_Sum A B.
(* from: originally defined by Hexirp *)

(** 依存直和型です。 *)

Definition matching_Dependent_Sum@{ i j | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( P : Type@{ j } ) ( cp : forall a : A, B a -> P ) ( x : Dependent_Sum A B ) : P := match x as x_ return P with pair_Dependent_Sum _ _ a b => cp a b end.
(* from: originally defined by Hexirp *)

(** 依存直和型の場合分けです。 *)

Definition identity_matching_Dependent_Sum@{ i j | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( P : Type@{ j } ) ( display : P -> Dependent_Sum A B ) ( cp : forall a : A, B a -> P ) ( icp : forall ( a : A ) ( b : B a ), Path ( Dependent_Sum A B ) ( display ( cp a b ) ) ( pair_Dependent_Sum A B a b ) ) ( x : Dependent_Sum A B ) : Path ( Dependent_Sum A B ) ( display ( matching_Dependent_Sum A B P cp x ) ) x := match x as x_ return Path ( Dependent_Sum A B ) ( display ( matching_Dependent_Sum A B P cp x_ ) ) x_ with pair_Dependent_Sum _ _ a b => icp a b end.
(* from: originally defined by Hexirp *)

(** 依存直和型の場合分けの恒等式です。 *)

Definition first_Dependent_Sum@{ i | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) : Dependent_Sum A B -> A := matching_Dependent_Sum A B A ( fun ( xf : A ) ( _ : B xf ) => xf ).
(* from: originally defined by Hexirp *)

(** 依存直和型の第一射影関数です。 *)

Definition second_Dependent_Sum@{ i | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( x : Dependent_Sum A B ) : B ( first_Dependent_Sum A B x ) := match x as x_ return B ( first_Dependent_Sum A B x_ ) with pair_Dependent_Sum _ _ xf xs => xs end.
(* from: originally defined by Hexirp *)

(** 依存直和型の第二射影関数です。 *)

Definition dependent_matching_Path@{ i j mij | i <= mij, j <= mij } ( A : Type@{ i } ) ( a : A ) ( P : forall a' : A, Path A a a' -> Type@{ j } ) ( ci : P a ( id_Path A a ) ) ( a' : A ) ( x : Path A a a' ) : P a' x := trpt_Path ( Path A a a' ) ( first_Dependent_Sum ( Path A a a' ) ( P a' ) ( matching_Path A a ( fun a' : A => Dependent_Sum@{ mij } ( Path A a a' ) ( P a' ) ) ( pair_Dependent_Sum ( Path A a a ) ( P a ) ( id_Path A a ) ci ) a' x ) ) x ( P a' ) ( identity_matching_Path A a ( fun a' : A => Dependent_Sum@{ mij } ( Path A a a' ) ( P a' ) ) ( fun a' : A => first_Dependent_Sum ( Path A a a' ) ( P a' ) ) ( pair_Dependent_Sum ( Path A a a ) ( P a ) ( id_Path A a ) ci ) ( id_Path ( Path A a a ) ( id_Path A a ) ) a' x ) ( second_Dependent_Sum ( Path A a a' ) ( P a' ) ( matching_Path A a ( fun a' : A => Dependent_Sum@{ mij } ( Path A a a' ) ( P a' ) ) ( pair_Dependent_Sum ( Path A a a ) ( P a ) ( id_Path A a ) ci ) a' x ) ).
(* from: originally defined by Hexirp *)

(** 道の依存場合分けです。 *)

Definition comatching_Dependent_Sum@{ i j | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( P : Type@{ j } ) ( df : P -> A ) ( ds : forall x : P, B ( df x ) ) ( x : P ) : Dependent_Sum A B := pair_Dependent_Sum A B ( df x ) ( ds x ).
(* from: originally defined by Hexirp *)

(** 依存直和型の余場合分けです。 *)

Fail Definition identity_comaching_Dependent_Sum@{ i j | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( P : Type@{ j } ) ( codisplay : Dependent_Sum A B -> P ) ( df : P -> A ) ( idf : forall x : Dependent_Sum A B, Path A ( df ( codisplay x ) ) ( first_Dependent_Sum A B x ) ) ( ds : forall x : P, B ( df x ) ) ( ids : forall x : Dependent_Sum A B, Path ( B ( df ( codisplay x ) ) ) ( ds ( codisplay x ) ) ( trpv_Path A ( df (codisplay x ) ) ( first_Dependent_Sum A B x ) B ( idf x ) ( second_Dependent_Sum A B x ) ) ) ( x : Dependent_Sum A B ) : Path ( Dependent_Sum A B ) ( comatching_Dependent_Sum A B P df ds ( codisplay x ) ) x := _.
(* from: originally defined by Hexirp *)

(** 依存直和型の余場合分けの恒等式です。ただし、これを実装するためには直積型の η 規則が必要であるため、今は実装できません。 *)

Definition map_Dependent_Sum@{ i | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( C : Type@{ i } ) ( D : C -> Type@{ i } ) ( f : A -> C ) ( g : forall x : A, B x -> D ( f x ) ) ( x : Dependent_Sum A B ) : Dependent_Sum C D := pair_Dependent_Sum C D ( f ( first_Dependent_Sum A B x ) ) ( g ( first_Dependent_Sum A B x ) ( second_Dependent_Sum A B x ) ).
(* from: originally defined by Hexirp *)

(** 依存直和型の写像です。 *)
