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

Definition first_Dependent_Sum@{ i | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( x : Dependent_Sum A B ) : A := match x with pair_Dependent_Sum _ _ a _ => a end.
(* from: originally defined by Hexirp *)

(** 依存直和型の第一射影関数です。 *)

Definition second_Dependent_Sum@{ i | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( x : Dependent_Sum A B ) : B ( first_Dependent_Sum A B x ) := match x as x_ return B ( first_Dependent_Sum A B x_ ) with pair_Dependent_Sum _ _ a b => b end.
(* from: originally defined by Hexirp *)

(** 依存直和型の第二射影関数です。 *)

Definition comatching_Dependent_Sum@{ i j | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( P : Type@{ j } ) ( df : P -> A ) ( ds : forall x : P, B ( df x ) ) ( x : P ) : Dependent_Sum A B := pair_Dependent_Sum A B ( df x ) ( ds x ).
(* from: originally defined by Hexirp *)

(** 依存直和型の余場合分けです。 *)

Fail Definition identity_comaching_Dependent_Sum@{ i j | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( P : Type@{ j } ) ( codisplay : Dependent_Sum A B -> P ) ( df : P -> A ) ( idf : forall x : Dependent_Sum A B, Path A ( df ( codisplay x ) ) ( first_Dependent_Sum A B x ) ) ( ds : forall x : P, B ( df x ) ) ( ids : forall x : Dependent_Sum A B, Path ( B ( df ( codisplay x ) ) ) ( ds ( codisplay x ) ) ( trpv_Path A ( df (codisplay x ) ) ( first_Dependent_Sum A B x ) B ( idf x ) ( second_Dependent_Sum A B x ) ) ) ( x : Dependent_Sum A B ) : Path ( Dependent_Sum A B ) ( comatching_Dependent_Sum A B P df ds ( codisplay x ) ) x := _.
(* from: originally defined by Hexirp *)

(** 依存直和型の余場合分けの恒等式です。これは証明に依存直和型の η 規則が必要であるため、ここでは証明できません。 *)

Definition map_Dependent_Sum@{ i | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( C : Type@{ i } ) ( D : C -> Type@{ i } ) ( f : A -> C ) ( g : forall x : A, B x -> D ( f x ) ) ( x : Dependent_Sum@{i} A B ) : Dependent_Sum@{i} C D := pair_Dependent_Sum C D ( f ( first_Dependent_Sum A B x ) ) ( g ( first_Dependent_Sum A B x ) ( second_Dependent_Sum A B x ) ).
(* from: originally defined by Hexirp *)

(** 依存直和型の写像です。 *)
