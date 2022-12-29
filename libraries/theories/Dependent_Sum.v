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
  refine ( matching_Dependent_Sum@{ i si } A B ( forall y_ : Dependent_Sum A B, Type@{ i } ) _ x y ).
  refine ( fun ( xf : A ) ( xs : B xf ) ( y_ : Dependent_Sum A B ) => _ ).
  refine ( matching_Dependent_Sum@{ i si } A B Type@{ i } _ y_ ).
  refine ( fun ( yf : A ) ( ys : B yf ) => _ ).
  exact ( Dependent_Sum ( Path A xf yf ) ( fun pf : Path A xf yf => Path ( B yf ) ( trpt_Path A B xf yf pf xs ) ys ) ).
Defined.
(* from: originally defined by Hexirp *)

(** 依存直和型の構築子の道です。 *)

Definition from_path_cons_Dependent_Sum@{ i si | i < si } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( x : Dependent_Sum A B ) ( y : Dependent_Sum A B ) ( p : path_cons_Dependent_Sum@{ i si } A B x y ) : Path ( Dependent_Sum A B ) x y.
Proof.
  refine ( dependent_matching_Dependent_Sum A B ( fun x_ : Dependent_Sum A B => forall ( y_ : Dependent_Sum A B ) ( p_ : path_cons_Dependent_Sum A B x_ y_ ), Path ( Dependent_Sum A B ) x_ y_ ) _ x y p ).
  refine ( fun ( xf : A ) ( xs : B xf ) ( y_ : Dependent_Sum A B ) ( p_ : path_cons_Dependent_Sum A B ( pair_Dependent_Sum A B xf xs ) y_ ) => _ ).
  refine ( dependent_matching_Dependent_Sum@{ i si } A B ( fun y__ : Dependent_Sum A B => forall p__ : path_cons_Dependent_Sum A B ( pair_Dependent_Sum A B xf xs ) y__, Path ( Dependent_Sum A B ) ( pair_Dependent_Sum A B xf xs ) y__ ) _ y_ p_ ).
  refine ( fun ( yf : A ) ( ys : B yf ) => _ ).
  change ( path_cons_Dependent_Sum A B ( pair_Dependent_Sum A B xf xs ) ( pair_Dependent_Sum A B yf ys ) -> Path ( Dependent_Sum A B ) ( pair_Dependent_Sum A B xf xs ) ( pair_Dependent_Sum A B yf ys ) ).
  change ( Dependent_Sum ( Path A xf yf ) ( fun pf : Path A xf yf => Path ( B yf ) ( trpt_Path A B xf yf pf xs ) ys ) -> Path ( Dependent_Sum A B ) ( pair_Dependent_Sum A B xf xs ) ( pair_Dependent_Sum A B yf ys ) ).
  refine ( fun p__ : Dependent_Sum ( Path A xf yf ) ( fun pf : Path A xf yf => Path ( B yf ) ( trpt_Path A B xf yf pf xs ) ys ) => _ ).
  refine ( matching_Dependent_Sum ( Path A xf yf ) ( fun pf : Path A xf yf => Path ( B yf ) ( trpt_Path A B xf yf pf xs ) ys ) ( Path ( Dependent_Sum A B ) ( pair_Dependent_Sum A B xf xs ) ( pair_Dependent_Sum A B yf ys ) ) _ p__ ).
  refine ( fun ( pf : Path A xf yf ) ( ps : Path ( B yf ) ( trpt_Path A B xf yf pf xs ) ys ) => _ ).
  refine ( dependent_matching_Path A xf ( fun ( yf_ : A ) ( pf_ : Path A xf yf_ ) => forall ( ys_ : B yf_ ) ( ps_ : Path ( B yf_ ) ( trpt_Path A B xf yf_ pf_ xs ) ys_ ), Path ( Dependent_Sum A B ) ( pair_Dependent_Sum A B xf xs ) ( pair_Dependent_Sum A B yf_ ys_ ) ) _ yf pf ys ps ).
  change ( forall ( ys_ : B xf ) ( ps_ : Path ( B xf ) ( trpt_Path A B xf xf ( id_Path A xf ) xs ) ys_ ), Path ( Dependent_Sum A B ) ( pair_Dependent_Sum A B xf xs ) ( pair_Dependent_Sum A B xf ys_ ) ).
  change ( forall ( ys_ : B xf ) ( ps_ : Path ( B xf ) xs ys_ ), Path ( Dependent_Sum A B ) ( pair_Dependent_Sum A B xf xs ) ( pair_Dependent_Sum A B xf ys_ ) ).
  refine ( fun ( ys_ : B xf ) ( ps_ : Path ( B xf ) xs ys_ ) => _ ).
  refine ( matching_Path ( B xf ) xs ( fun ys__ : B xf => Path ( Dependent_Sum A B ) ( pair_Dependent_Sum A B xf xs ) ( pair_Dependent_Sum A B xf ys__ ) ) _ ys_ ps_ ).
  exact ( id_Path ( Dependent_Sum A B ) ( pair_Dependent_Sum A B xf xs ) ).
Defined.
(* from: originally defined by Hexirp *)

(** 依存直和型の構築子の道から依存直和型の道への関数です。 *)

Definition first_Dependent_Sum@{ i | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( x : Dependent_Sum A B ) : A := matching_Dependent_Sum A B A ( fun ( xf : A ) ( _ : B xf ) => xf ) x.
(* from: originally defined by Hexirp *)

(** 依存直和型の第一射影関数（分解子）です。 *)

Definition second_Dependent_Sum@{ i | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( x : Dependent_Sum A B ) : B ( first_Dependent_Sum A B x ) := dependent_matching_Dependent_Sum A B ( fun x_ : Dependent_Sum A B => B ( first_Dependent_Sum A B x_ ) ) ( fun ( xf : A ) ( xs : B xf ) => xs ) x.
(* from: originally defined by Hexirp *)

(** 依存直和型の第二射影関数（分解子）です。 *)

Definition path_dest_Dependent_Sum@{ i | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( x : Dependent_Sum A B ) ( y : Dependent_Sum A B ) : Type@{ i } := Dependent_Sum ( Path A ( first_Dependent_Sum A B x ) ( first_Dependent_Sum A B y ) ) ( fun pf : Path A ( first_Dependent_Sum A B x ) ( first_Dependent_Sum A B y ) => Path ( B ( first_Dependent_Sum A B y ) ) ( trpt_Path A B ( first_Dependent_Sum A B x ) ( first_Dependent_Sum A B y ) pf ( second_Dependent_Sum A B x ) ) ( second_Dependent_Sum A B y ) ).
(* from: originally defined by Hexirp *)

(** 依存直和型の分解子の道です。 *)

Definition from_path_dest_Dependent_Sum@{ i | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( x : Dependent_Sum A B ) ( y : Dependent_Sum A B ) ( p : path_dest_Dependent_Sum A B x y ) : Path ( Dependent_Sum A B ) x y.
Proof.
  refine ( dependent_matching_Dependent_Sum A B ( fun x_ : Dependent_Sum A B => forall ( y_ : Dependent_Sum A B ) ( p_ : path_dest_Dependent_Sum A B x_ y_ ), Path ( Dependent_Sum A B ) x_ y_ ) _ x y p ).
  refine ( fun ( xf : A ) ( xs : B xf ) ( y_ : Dependent_Sum A B ) ( p_ : path_dest_Dependent_Sum A B ( pair_Dependent_Sum A B xf xs ) y_ ) => _ ).
  refine ( dependent_matching_Dependent_Sum A B ( fun y__ : Dependent_Sum A B => forall ( p__ : path_dest_Dependent_Sum A B ( pair_Dependent_Sum A B xf xs ) y__ ), Path ( Dependent_Sum A B ) ( pair_Dependent_Sum A B xf xs ) y__ ) _ y_ p_ ).
  refine ( fun ( yf : A ) ( ys : B yf ) => _ ).
  change ( path_dest_Dependent_Sum A B ( pair_Dependent_Sum A B xf xs ) ( pair_Dependent_Sum A B yf ys ) -> Path ( Dependent_Sum A B ) ( pair_Dependent_Sum A B xf xs ) ( pair_Dependent_Sum A B yf ys ) ).
  change ( Dependent_Sum ( Path A ( first_Dependent_Sum A B ( pair_Dependent_Sum A B xf xs ) ) ( first_Dependent_Sum A B ( pair_Dependent_Sum A B yf ys ) ) ) ( fun pf : Path A ( first_Dependent_Sum A B ( pair_Dependent_Sum A B xf xs ) ) ( first_Dependent_Sum A B ( pair_Dependent_Sum A B yf ys ) ) => Path ( B ( first_Dependent_Sum A B ( pair_Dependent_Sum A B yf ys ) ) ) ( trpt_Path A B ( first_Dependent_Sum A B ( pair_Dependent_Sum A B xf xs ) ) ( first_Dependent_Sum A B ( pair_Dependent_Sum A B yf ys ) ) pf ( second_Dependent_Sum A B ( pair_Dependent_Sum A B xf xs ) ) ) ( second_Dependent_Sum A B ( pair_Dependent_Sum A B yf ys ) ) ) -> Path ( Dependent_Sum A B ) ( pair_Dependent_Sum A B xf xs ) ( pair_Dependent_Sum A B yf ys ) ).
  change ( Dependent_Sum ( Path A xf yf ) ( fun pf : Path A xf yf => Path ( B yf ) ( trpt_Path A B xf yf pf xs ) ys ) -> Path ( Dependent_Sum A B ) ( pair_Dependent_Sum A B xf xs ) ( pair_Dependent_Sum A B yf ys ) ).
  refine ( fun p__ : Dependent_Sum ( Path A xf yf ) ( fun pf : Path A xf yf => Path ( B yf ) ( trpt_Path A B xf yf pf xs ) ys ) => _ ).
  refine ( matching_Dependent_Sum ( Path A xf yf ) ( fun pf : Path A xf yf => Path ( B yf ) ( trpt_Path A B xf yf pf xs ) ys ) ( Path ( Dependent_Sum A B ) ( pair_Dependent_Sum A B xf xs ) ( pair_Dependent_Sum A B yf ys ) ) _ p__ ).
  refine ( fun ( pf : Path A xf yf ) ( ps : Path ( B yf ) ( trpt_Path A B xf yf pf xs ) ys ) => _ ).
  refine ( dependent_matching_Path A xf ( fun ( yf_ : A ) ( pf_ : Path A xf yf_ ) => forall ( ys_ : B yf_ ) ( ps_ : Path ( B yf_ ) ( trpt_Path A B xf yf_ pf_ xs ) ys_ ), Path ( Dependent_Sum A B ) ( pair_Dependent_Sum A B xf xs ) ( pair_Dependent_Sum A B yf_ ys_ ) ) _ yf pf ys ps ).
  change ( forall ( ys_ : B xf ) ( ps_ : Path ( B xf ) ( trpt_Path A B xf xf ( id_Path A xf ) xs ) ys_ ), Path ( Dependent_Sum A B ) ( pair_Dependent_Sum A B xf xs ) ( pair_Dependent_Sum A B xf ys_ ) ).
  change ( forall ( ys_ : B xf ) ( ps_ : Path ( B xf ) xs ys_ ), Path ( Dependent_Sum A B ) ( pair_Dependent_Sum A B xf xs ) ( pair_Dependent_Sum A B xf ys_ ) ).
  refine ( fun ( ys_ : B xf ) ( ps_ : Path ( B xf ) xs ys_ ) => _ ).
  refine ( matching_Path ( B xf ) xs ( fun ys__ : B xf => Path ( Dependent_Sum A B ) ( pair_Dependent_Sum A B xf xs ) ( pair_Dependent_Sum A B xf ys__ ) ) _ ys_ ps_ ).
  exact ( id_Path ( Dependent_Sum A B ) ( pair_Dependent_Sum A B xf xs ) ).
Defined.
(* from: originally defined by Hexirp *)

(** 依存直和型の分解子の道から依存直和型の道への関数です。 *)

Definition comatching_Dependent_Sum@{ i j | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( P : Type@{ j } ) ( df : P -> A ) ( ds : forall x : P, B ( df x ) ) ( x : P ) : Dependent_Sum A B := pair_Dependent_Sum A B ( df x ) ( ds x ).
(* from: originally defined by Hexirp *)

(** 依存直和型の余場合分けです。 *)

Definition identity_comaching_Dependent_Sum@{ i j | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( P : Type@{ j } ) ( codisplay : Dependent_Sum A B -> P ) ( df : P -> A ) ( idf : forall x : Dependent_Sum A B, Path A ( df ( codisplay x ) ) ( first_Dependent_Sum A B x ) ) ( ds : forall x : P, B ( df x ) ) ( ids : forall x : Dependent_Sum A B, Path ( B ( first_Dependent_Sum A B x ) ) ( trpt_Path A B ( df ( codisplay x ) ) ( first_Dependent_Sum A B x ) ( idf x ) ( ds ( codisplay x ) ) ) ( second_Dependent_Sum A B x ) ) ( x : Dependent_Sum A B ) : Path ( Dependent_Sum A B ) ( comatching_Dependent_Sum A B P df ds ( codisplay x ) ) x.
Proof.
  refine ( dependent_matching_Dependent_Sum A B ( fun x_ : Dependent_Sum A B => Path ( Dependent_Sum A B ) ( comatching_Dependent_Sum A B P df ds ( codisplay x_ ) ) x_ ) _ x ).
  refine ( fun ( xf : A ) ( xs : B xf ) => _ ).
  refine ( from_path_dest_Dependent_Sum A B ( comatching_Dependent_Sum A B P df ds ( codisplay ( pair_Dependent_Sum A B xf xs ) ) ) ( pair_Dependent_Sum A B xf xs ) _ ).
  change ( path_dest_Dependent_Sum A B ( comatching_Dependent_Sum A B P df ds ( codisplay ( pair_Dependent_Sum A B xf xs ) ) ) ( pair_Dependent_Sum A B xf xs ) ).
  change ( Dependent_Sum ( Path A ( first_Dependent_Sum A B ( comatching_Dependent_Sum A B P df ds ( codisplay ( pair_Dependent_Sum A B xf xs ) ) ) ) ( first_Dependent_Sum A B ( pair_Dependent_Sum A B xf xs ) ) ) ( fun pf : Path A ( first_Dependent_Sum A B ( comatching_Dependent_Sum A B P df ds ( codisplay ( pair_Dependent_Sum A B xf xs ) ) ) ) ( first_Dependent_Sum A B ( pair_Dependent_Sum A B xf xs ) ) => Path ( B ( first_Dependent_Sum A B ( pair_Dependent_Sum A B xf xs ) ) ) ( trpt_Path A B ( first_Dependent_Sum A B ( comatching_Dependent_Sum A B P df ds ( codisplay ( pair_Dependent_Sum A B xf xs ) ) ) ) ( first_Dependent_Sum A B ( pair_Dependent_Sum A B xf xs ) ) pf ( second_Dependent_Sum A B ( comatching_Dependent_Sum A B P df ds ( codisplay ( pair_Dependent_Sum A B xf xs ) ) ) ) ) ( second_Dependent_Sum A B ( pair_Dependent_Sum A B xf xs ) ) ) ).
  change ( Dependent_Sum ( Path A ( df ( codisplay ( pair_Dependent_Sum A B xf xs ) ) ) xf ) ( fun pf : Path A ( df ( codisplay ( pair_Dependent_Sum A B xf xs ) ) ) xf => Path ( B xf ) ( trpt_Path A B ( df ( codisplay ( pair_Dependent_Sum A B xf xs ) ) ) xf pf ( ds ( codisplay ( pair_Dependent_Sum A B xf xs ) ) ) ) xs ) ).
  refine ( pair_Dependent_Sum ( Path A ( df ( codisplay ( pair_Dependent_Sum A B xf xs ) ) ) xf ) ( fun pf : Path A ( df ( codisplay ( pair_Dependent_Sum A B xf xs ) ) ) xf => Path ( B xf ) ( trpt_Path A B ( df ( codisplay ( pair_Dependent_Sum A B xf xs ) ) ) xf pf ( ds ( codisplay ( pair_Dependent_Sum A B xf xs ) ) ) ) xs ) ?[pf] _ ).
  [pf]: {
    change ( Path A ( df ( codisplay ( pair_Dependent_Sum A B xf xs ) ) ) xf ).
    change ( Path A ( df ( codisplay ( pair_Dependent_Sum A B xf xs ) ) ) ( first_Dependent_Sum A B ( pair_Dependent_Sum A B xf xs ) ) ).
    exact ( idf ( pair_Dependent_Sum A B xf xs ) ).
  }
  change ( Path ( B xf ) ( trpt_Path A B ( df ( codisplay ( pair_Dependent_Sum A B xf xs ) ) ) xf ( idf ( pair_Dependent_Sum A B xf xs ) ) ( ds ( codisplay ( pair_Dependent_Sum A B xf xs ) ) ) ) xs ).
  change ( Path ( B xf ) ( trpt_Path A B ( df ( codisplay ( pair_Dependent_Sum A B xf xs ) ) ) xf ( idf ( pair_Dependent_Sum A B xf xs ) ) ( ds ( codisplay ( pair_Dependent_Sum A B xf xs ) ) ) ) ( second_Dependent_Sum A B ( pair_Dependent_Sum A B xf xs ) ) ).
  exact ( ids ( pair_Dependent_Sum A B xf xs ) ).
Defined.
(* from: originally defined by Hexirp *)

(** 依存直和型の余場合分けの恒等式です。 *)

Definition curry_Product@{ i j | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( C : Type@{ j } ) ( f : Dependent_Sum A B -> C ) ( x : A ) ( y : B x ) : C := f ( pair_Dependent_Sum A B x y ).
(* from: originally defined by Hexirp *)

(** 依存直和型のカリー化です。 *)

Definition uncurry_Product@{ i j | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( C : Type@{ j } ) ( f : forall x : A, B x -> C ) ( x : Dependent_Sum A B ) : C := matching_Dependent_Sum@{ i j } A B C ( fun ( xf : A ) ( xs : B xf ) => f xf xs ) x.
(* from: originally defined by Hexirp *)

(** 依存直和型の非カリー化です。 *)

Definition map_Dependent_Sum@{ i j | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( C : Type@{ j } ) ( D : C -> Type@{ j } ) ( f : A -> C ) ( g : forall x : A, B x -> D ( f x ) ) ( x : Dependent_Sum A B ) : Dependent_Sum C D := pair_Dependent_Sum C D ( f ( first_Dependent_Sum A B x ) ) ( g ( first_Dependent_Sum A B x ) ( second_Dependent_Sum A B x ) ).
(* from: originally defined by Hexirp *)

(** 依存直和型の写像です。 *)
