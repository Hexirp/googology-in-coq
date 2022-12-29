(** 直和型に関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Path.
Require Googology_In_Coq.Void.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Path.
Import Googology_In_Coq.Void.

(** ライブラリを開きます。 *)

Inductive Sum@{ i | } ( A : Type@{ i } ) ( B : Type@{ i } ) : Type@{ i } := left_Sum : A -> Sum A B | right_Sum : B -> Sum A B.
(* from: originally defined by Hexirp *)

(** 直和型です。 *)

Definition matching_Sum@{ i j | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( P : Type@{ j } ) ( cl : A -> P ) ( cr : B -> P ) ( x : Sum A B ) : P := match x with left_Sum _ _ xl => cl xl | right_Sum _ _ xr => cr xr end.
(* from: originally defined by Hexirp *)

(** 直和型の場合分けです。 *)

Definition identity_matching_Sum@{ i j | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( P : Type@{ j } ) ( display : P -> Sum A B ) ( cl : A -> P ) ( icl : forall xl : A, Path ( Sum A B ) ( display ( cl xl ) ) ( left_Sum A B xl ) ) ( cr : B -> P ) ( icr : forall xr : B, Path ( Sum A B ) ( display ( cr xr ) ) ( right_Sum A B xr ) ) ( x : Sum A B ) : Path ( Sum A B ) ( display ( matching_Sum A B P cl cr x ) ) x := match x as x_ return Path ( Sum A B ) ( display ( matching_Sum A B P cl cr x_ ) ) x_ with left_Sum _ _ xl => icl xl | right_Sum _ _ xr => icr xr end.
(* from: originally defined by Hexirp *)

(** 直和型の場合分けです。 *)

Definition dependent_matching_Sum@{ i j | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( P : Sum A B -> Type@{ j } ) ( cl : forall xl : A, P ( left_Sum A B xl ) ) ( cr : forall xr : B, P ( right_Sum A B xr ) ) ( x : Sum A B ) : P x := match x as x_ return P x_ with left_Sum _ _ xl => cl xl | right_Sum _ _ xr => cr xr end.
(* from: originally defined by Hexirp *)

(** 直和型の依存場合分けです。 *)

Definition path_cons_Sum@{ i si | i < si } ( A : Type@{ i } ) ( B : Type@{ i } ) ( x : Sum A B ) ( y : Sum A B ) : Type@{ i }.
Proof.
  refine ( matching_Sum@{ i si } A B ( forall y_ : Sum A B, Type@{ i } ) _ _ x y ).
  -
    refine ( fun ( xl : A ) ( y_ : Sum A B ) => _ ).
    refine ( matching_Sum@{ i si } A B Type@{ i } _ _ y_ ).
    +
      refine ( fun yl : A => _ ).
      exact ( Path A xl yl ).
    +
      refine ( fun yr : B => _ ).
      exact Void@{ i }.
  -
    refine ( fun ( xr : B ) ( y_ : Sum A B ) => _ ).
    refine ( matching_Sum@{ i si } A B Type@{ i } _ _ y_ ).
    +
      refine ( fun yl : A => _ ).
      exact Void@{ i }.
    +
      refine ( fun yr : B => _ ).
      exact ( Path B xr yr ).
Defined.
(* from: originally defined by Hexirp *)

(** 直和型の構築子の道です。 *)

Definition from_path_cons_Sum@{ i si | i < si } ( A : Type@{ i } ) ( B : Type@{ i } ) ( x : Sum A B ) ( y : Sum A B ) ( p : path_cons_Sum@{ i si } A B x y ) : Path ( Sum A B ) x y.
Proof.
  refine ( dependent_matching_Sum A B ( fun x_ : Sum A B => forall ( y_ : Sum A B ) ( p_ : path_cons_Sum@{ i si } A B x_ y_ ), Path ( Sum A B ) x_ y_ ) _ _ x y p ).
  -
    refine ( fun ( xl : A ) ( y_ : Sum A B ) ( p_ : path_cons_Sum@{ i si } A B ( left_Sum A B xl ) y_ ) => _ ).
    refine ( dependent_matching_Sum A B ( fun y__ : Sum A B => forall p__ : path_cons_Sum@{ i si } A B ( left_Sum A B xl ) y__, Path ( Sum A B ) ( left_Sum A B xl ) y__ ) _ _ y_ p_ ).
    +
      refine ( fun yl : A => _ ).
      change ( path_cons_Sum@{ i si } A B ( left_Sum A B xl ) ( left_Sum A B yl ) -> Path ( Sum A B ) ( left_Sum A B xl ) ( left_Sum A B yl ) ).
      change ( Path A xl yl -> Path ( Sum A B ) ( left_Sum A B xl ) ( left_Sum A B yl ) ).
      refine ( fun p__ : Path A xl yl => _ ).
      exact ( ap_Path A ( Sum A B ) ( left_Sum A B ) xl yl p__ ).
    +
      refine ( fun yr : B => _ ).
      change ( path_cons_Sum@{ i si } A B ( left_Sum A B xl ) ( right_Sum A B yr ) -> Path ( Sum A B ) ( left_Sum A B xl ) ( right_Sum A B yr ) ).
      change ( Void@{ i } -> Path ( Sum A B ) ( left_Sum A B xl ) ( right_Sum A B yr ) ).
      refine ( fun p__ : Void@{ i } => _ ).
      exact ( absurd_Void ( Path ( Sum A B ) ( left_Sum A B xl ) ( right_Sum A B yr ) ) p__ ).
  -
    refine ( fun ( xr : B ) ( y_ : Sum A B ) ( p_ : path_cons_Sum@{ i si } A B ( right_Sum A B xr ) y_ ) => _ ).
    refine ( dependent_matching_Sum A B ( fun y__ : Sum A B => forall p__ : path_cons_Sum@{ i si } A B ( right_Sum A B xr ) y__, Path ( Sum A B ) ( right_Sum A B xr ) y__ ) _ _ y_ p_ ).
    +
      refine ( fun yl : A => _ ).
      change ( path_cons_Sum@{ i si } A B ( right_Sum A B xr ) ( left_Sum A B yl ) -> Path ( Sum A B ) ( right_Sum A B xr ) ( left_Sum A B yl ) ).
      change ( Void@{ i } -> Path ( Sum A B ) ( right_Sum A B xr ) ( left_Sum A B yl ) ).
      refine ( fun p__ : Void@{ i } => _ ).
      exact ( absurd_Void ( Path ( Sum A B ) ( right_Sum A B xr ) ( left_Sum A B yl ) ) p__ ).
    +
      refine ( fun yr : B => _ ).
      change ( path_cons_Sum@{ i si } A B ( right_Sum A B xr ) ( right_Sum A B yr ) -> Path ( Sum A B ) ( right_Sum A B xr ) ( right_Sum A B yr ) ).
      change ( Path B xr yr -> Path ( Sum A B ) ( right_Sum A B xr ) ( right_Sum A B yr ) ).
      refine ( fun p__ : Path B xr yr => _ ).
      exact ( ap_Path B ( Sum A B ) ( right_Sum A B ) xr yr p__ ).
Defined.
(* from: originally defined by Hexirp *)

(** 直和型の構築子の道から直和型の道を作る関数です。 *)

Definition map_Sum@{ i j | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( C : Type@{ j } ) ( D : Type@{ j } ) ( f : A -> C ) ( g : B -> D ) : Sum A B -> Sum C D := matching_Sum A B ( Sum C D ) ( fun xl : A => left_Sum C D ( f xl ) ) ( fun xr : B => right_Sum C D ( g xr ) ).
(* from: originally defined by Hexirp *)

(** 直和型の写像です。 *)
