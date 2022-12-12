(** 依存直和型に関するモジュールです。 *)

Require Googology_In_Coq.Base.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.

(** ライブラリを開きます。 *)

Inductive Dependent_Sum@{ i | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) : Type@{ i } := pair_Dependent_Sum : forall a : A, B a -> Dependent_Sum A B.
(* from: originally defined by Hexirp *)

(** 依存直和型です。 *)

Definition matching_Dependent_Sum@{ i j | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( P : Type@{ j } ) ( cp : forall a : A, B a -> P ) ( x : Dependent_Sum A B ) : P := match x as x_ return P with pair_Dependent_Sum _ _ a b => cp a b end.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition equality_matching_Dependent_Sum@{ i j | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( P : Type@{ j } ) ( display : P -> Dependent_Sum A B ) ( cp : forall a : A, B a -> P ) ( ecp : forall ( a : A ) ( b : B a ), display ( cp a b ) = pair_Dependent_Sum a b ) ( x : Dependent_Sum A B ) : display ( matching_Dependent_Sum A B P cp x ) = x := match x as x_ return P with pair_Dependent_Sum _ _ a b => cp a b end.
(* from: originally defined by Hexirp *)

(** 場合分けの等式です。 *)

Definition comaching_Dependent_Sum@{ i j | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( P : Type@{ j } ) ( df : P -> A ) ( ds : forall x : P, B ( df x ) ) ( x : P ) : Dependent_Sum A B := pair_Dependent_Sum A B ( df x ) ( ds x ).
(* from: originally defined by Hexirp *)

(** 余場合分けです。 *)

Definition first_Dependent_Sum@{ i | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) : Dependent_Sum A B -> A := matching A B A ( fun ( a : A ) ( b : B a ) => a ).
(* from: originally defined by Hexirp *)

(** 依存直和型の第一射影関数です。 *)

Definition
  second@{i | } (A : Type@{i}) (B : A -> Type@{i})
    : forall x : Dependent_Sum A B, B (first A B x)
    :=
      matching
        A
        B
        (fun x_ : Dependent_Sum A B => B (first A B x_))
        (fun (a : A) (b : B a) => b)
.
(* from: originally defined by Hexirp *)

(** 依存直和型の第二射影関数です。 *)

Definition map_Dependent_Sum@{ i | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( C : Type@{ i } ) ( D : C -> Type@{ i } ) ( f : A -> C ) ( g : forall x : A, B x -> D ( f x ) ) ( x : Dependent_Sum@{i} A B ) : Dependent_Sum@{i} C D := pair_Dependent_Sum C D ( f ( first_Dependent_Sum A B x ) ) ( g ( first_Dependent_Sum A B x ) ( second A B x ) ).
(* from: originally defined by Hexirp *)

(** 依存直和型の写像です。 *)
