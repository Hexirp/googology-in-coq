(** 依存直和型に関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Path.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Path.

(** ライブラリを開きます。 *)

Inductive Dependent_Sum@{ i | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) : Type@{ i } := pair_Dependent_Sum : forall xf : A, B xf -> Dependent_Sum A B.
(* from: originally defined by Hexirp *)

(** 依存直和型です。 *)

Definition matching_Dependent_Sum@{ i j | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( P : Type@{ j } ) ( cp : forall xf : A, B xf -> P ) ( x : Dependent_Sum A B ) : P := match x with pair_Dependent_Sum _ _ xf xs => cp xf xs end.
(* from: originally defined by Hexirp *)

(** 依存直和型の場合分けです。 *)

Definition identity_matching_Dependent_Sum@{ i j | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( P : Type@{ j } ) ( display : P -> Dependent_Sum A B ) ( cp : forall xf : A, B xf -> P ) ( icp : forall ( xf : A ) ( xs : B xf ), Path ( Dependent_Sum A B ) ( display ( cp xf xs ) ) ( pair_Dependent_Sum A B xf xs ) ) ( x : Dependent_Sum A B ) : Path ( Dependent_Sum A B ) ( display ( matching_Dependent_Sum A B P cp x ) ) x := match x as x_ return Path ( Dependent_Sum A B ) ( display ( matching_Dependent_Sum A B P cp x_ ) ) x_ with pair_Dependent_Sum _ _ xf xs => icp xf xs end.
(* from: originally defined by Hexirp *)

(** 依存直和型の場合分けの恒等式です。 *)

Definition dependent_matching_Dependent_Sum@{ i j | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( P : Dependent_Sum A B -> Type@{ j } ) ( cp : forall ( xf : A ) ( xs : B xf ), P ( pair_Dependent_Sum A B xf xs ) ) ( x : Dependent_Sum A B ) : P x := match x as x_ return P x_ with pair_Dependent_Sum _ _ xf xs => cp xf xs end.
(* from: originally defined by Hexirp *)

(** 依存直和型の依存場合分けです。 *)

Definition path_cons_Dependent_Sum@{ i si | i < si } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( x : Dependent_Sum A B ) ( y : Dependent_Sum A B ) : Type@{ i }.
Proof.
  exact _.
Defined.
(* from: originally defined by Hexirp *)

(** 依存直和型の構築子の関数です。 *)

Definition first_Dependent_Sum@{ i | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( x : Dependent_Sum A B ) : A := matching_Dependent_Sum A B A ( fun ( xf : A ) ( _ : B xf ) => xf ) x.
(* from: originally defined by Hexirp *)

(** 依存直和型の第一射影関数です。 *)

Definition second_Dependent_Sum@{ i | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( x : Dependent_Sum A B ) : B ( first_Dependent_Sum A B x ) := match x as x_ return B ( first_Dependent_Sum A B x_ ) with pair_Dependent_Sum _ _ xf xs => xs end.
(* from: originally defined by Hexirp *)

(** 依存直和型の第二射影関数です。 *)

Definition comatching_Dependent_Sum@{ i j | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( P : Type@{ j } ) ( df : P -> A ) ( ds : forall x : P, B ( df x ) ) ( x : P ) : Dependent_Sum A B := pair_Dependent_Sum A B ( df x ) ( ds x ).
(* from: originally defined by Hexirp *)

(** 依存直和型の余場合分けです。 *)

Fail Definition identity_comaching_Dependent_Sum@{ i j | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( P : Type@{ j } ) ( codisplay : Dependent_Sum A B -> P ) ( df : P -> A ) ( idf : forall x : Dependent_Sum A B, Path A ( df ( codisplay x ) ) ( first_Dependent_Sum A B x ) ) ( ds : forall x : P, B ( df x ) ) ( ids : forall x : Dependent_Sum A B, Path ( B ( df ( codisplay x ) ) ) ( ds ( codisplay x ) ) ( trpv_Path A ( df (codisplay x ) ) ( first_Dependent_Sum A B x ) B ( idf x ) ( second_Dependent_Sum A B x ) ) ) ( x : Dependent_Sum A B ) : Path ( Dependent_Sum A B ) ( comatching_Dependent_Sum A B P df ds ( codisplay x ) ) x := _.
(* from: originally defined by Hexirp *)

(** 依存直和型の余場合分けの恒等式です。ただし、これを実装するためには直積型の η 規則が必要であるため、今は実装できません。 *)

Definition map_Dependent_Sum@{ i | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( C : Type@{ i } ) ( D : C -> Type@{ i } ) ( f : A -> C ) ( g : forall x : A, B x -> D ( f x ) ) ( x : Dependent_Sum A B ) : Dependent_Sum C D := pair_Dependent_Sum C D ( f ( first_Dependent_Sum A B x ) ) ( g ( first_Dependent_Sum A B x ) ( second_Dependent_Sum A B x ) ).
(* from: originally defined by Hexirp *)

(** 依存直和型の写像です。 *)
