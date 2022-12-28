(** 直積型に関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Path.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Path.

(** ライブラリを開きます。 *)

Inductive Product@{ i | } ( A : Type@{ i } ) ( B : Type@{ i } ) : Type@{ i } := pair_Product : A -> B -> Product A B.
(* from: originally defined by Hexirp *)

(** 直積型です。 *)

Definition matching_Product@{ i j | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( P : Type@{ j } ) ( cp : A -> B -> P ) ( x : Product A B ) : P := match x with pair_Product _ _ xf xs => cp xf xs end.
(* from: originally defined by Hexirp *)

(** 直積型の場合分けです。 *)

Definition identity_matching_Product@{ i j | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( P : Type@{ j } ) ( display : P -> Product A B ) (cp : A -> B -> P ) ( icp : forall ( xf : A ) ( xs : B ), Path ( Product A B ) ( display ( cp xf xs ) ) ( pair_Product A B xf xs ) ) ( x : Product A B ) : Path ( Product A B ) ( display ( matching_Product A B P cp x ) ) x := match x as x_ return Path ( Product A B ) ( display ( matching_Product A B P cp x_ ) ) x_ with pair_Product _ _ xf xs => icp xf xs end.
(* from: originally defined by Hexirp *)

(** 直積型の場合分けの恒等式です。 *)

Definition dependent_matching_Product@{ i j | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( P : Product A B -> Type@{ j } ) ( cp : forall ( xf : A ) ( xs : B ), P ( pair_Product A B xf xs ) ) ( x : Product A B ) : P x := match x as x_ return P x_ with pair_Product _ _ xf xs => cp xf xs end.
(* from: originally defined by Hexirp *)

(** 直積型の依存場合分けです。 *)

Definition path_cons_Product@{ i si | i < si } ( A : Type@{ i } ) ( B : Type@{ i } ) ( x : Product A B ) ( y : Product A B ) : Type@{ i }.
Proof.
  refine ( matching_Product@{ i si } A B ( forall y_ : Product A B, Type@{ i } ) _ x y ).
  refine ( fun ( xf : A ) ( xs : B ) ( y_ : Product A B ) => _ ).
  refine ( matching_Product@{ i si } A B Type@{ i } _ y_ ).
  refine ( fun ( yf : A ) ( ys : B ) => _ ).
  exact ( Product ( Path A xf yf ) ( Path B xs ys ) ).
Defined.
(* from: originally defined by Hexirp *)

(** 直積型の構成子の道です。 *)

Definition from_path_cons_Product@{ i si | i < si } ( A : Type@{ i } ) ( B : Type@{ i } ) ( x : Product A B ) ( y : Product A B ) ( p : path_cons_Product@{ i si } A B x y ) : Path ( Product A B ) x y.
Proof.
  refine ( dependent_matching_Product A B ( fun x_ : Product A B => forall ( y_ : Product A B ) ( p_ : path_cons_Product@{ i si } A B x_ y_ ), Path ( Product A B ) x_ y_ ) _ x y p ).
  refine ( fun ( xf : A ) ( xs : B ) ( y_ : Product A B ) ( p_ : path_cons_Product@{ i si } A B ( pair_Product A B xf xs ) y_ ) => _ ).
  refine ( dependent_matching_Product A B ( fun y__ : Product A B => forall p__ : path_cons_Product@{ i si } A B ( pair_Product A B xf xs ) y__, Path ( Product A B ) ( pair_Product A B xf xs ) y__ ) _ y_ p_ ).
  refine ( fun ( yf : A ) ( ys : B ) => _ ).
  change ( path_cons_Product@{ i si } A B ( pair_Product A B xf xs ) ( pair_Product A B yf ys ) -> Path ( Product A B ) ( pair_Product A B xf xs ) ( pair_Product A B yf ys ) ).
  change ( Product ( Path A xf yf ) ( Path B xs ys ) -> Path ( Product A B ) ( pair_Product A B xf xs ) ( pair_Product A B yf ys ) ).
  refine ( fun p__ : Product ( Path A xf yf ) ( Path B xs ys ) => _ ).
  refine ( matching_Product ( Path A xf yf ) ( Path B xs ys ) ( Path ( Product A B ) ( pair_Product A B xf xs ) ( pair_Product A B yf ys ) ) _ p__ ).
  refine ( fun ( pf : Path A xf yf ) ( ps : Path B xs ys ) => _ ).
  exact ( trpt_2_Path A B ( fun ( yf_ : A ) ( ys_ : B ) => Path ( Product A B ) ( pair_Product A B xf xs ) ( pair_Product A B yf_ ys_ ) ) xf yf pf xs ys ps ( id_Path ( Product A B ) ( pair_Product A B xf xs ) ) ).
Defined.
(* from: originally defined by Hexirp *)

(** 直積型の構成子の道から直積型の道への関数です。 *)

Definition first_Product@{ i | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( x : Product A B ) : A := matching_Product A B A ( fun ( xf : A ) ( xs : B ) => xf ) x.
(* from: originally defined by Hexirp *)

(** 直積型の第一射影関数（分解子）です。 *)

Definition second_Product@{ i | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( x : Product A B ) : B := matching_Product A B B ( fun ( xf : A ) ( xs : B ) => xs ) x.
(* from: originally defined by Hexirp *)

(** 直積型の第二射影関数（分解子）です。 *)

Definition path_dest_Product@{ i | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( x : Product A B ) ( y : Product A B ) : Type@{ i } := Product ( Path A ( first_Product A B x ) ( first_Product A B y ) ) ( Path B ( second_Product A B x ) ( second_Product A B y ) ).
(* from: originally defined by Hexirp *)

(** 直積型の分解子の道です。 *)

Definition from_path_dest_Product@{ i | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( x : Product A B ) ( y : Product A B ) ( p : path_dest_Product A B x y ) : Path ( Product A B ) x y.
Proof.
  refine ( dependent_matching_Product A B ( fun x_ : Product A B => forall ( y_ : Product A B ) ( p_ : path_dest_Product A B x_ y_ ), Path ( Product A B ) x_ y_ ) _ x y p ).
  refine ( fun ( xf : A ) ( xs : B ) ( y_ : Product A B ) ( p_ : path_dest_Product@{ i } A B ( pair_Product A B xf xs ) y_ ) => _ ).
  refine ( dependent_matching_Product A B ( fun y__ : Product A B => forall p__ : path_dest_Product A B ( pair_Product A B xf xs ) y__, Path ( Product A B ) ( pair_Product A B xf xs ) y__ ) _ y_ p_ ).
  refine ( fun ( yf : A ) ( ys : B ) => _ ).
  change ( path_cons_Product A B ( pair_Product A B xf xs ) ( pair_Product A B yf ys ) -> Path ( Product A B ) ( pair_Product A B xf xs ) ( pair_Product A B yf ys ) ).
  change ( Product ( Path A xf yf ) ( Path B xs ys ) -> Path ( Product A B ) ( pair_Product A B xf xs ) ( pair_Product A B yf ys ) ).
  refine ( fun p__ : Product ( Path A xf yf ) ( Path B xs ys ) => _ ).
  refine ( matching_Product ( Path A xf yf ) ( Path B xs ys ) ( Path ( Product A B ) ( pair_Product A B xf xs ) ( pair_Product A B yf ys ) ) _ p__ ).
  refine ( fun ( pf : Path A xf yf ) ( ps : Path B xs ys ) => _ ).
  exact ( trpt_2_Path A B ( fun ( yf_ : A ) ( ys_ : B ) => Path ( Product A B ) ( pair_Product A B xf xs ) ( pair_Product A B yf_ ys_ ) ) xf yf pf xs ys ps ( id_Path ( Product A B ) ( pair_Product A B xf xs ) ) ).
Defined.
(* from: originally defined by Hexirp *)

(** 直積型の分解子の道です。 *)

Definition comatching_Product@{ i j | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( P : Type@{ j } ) ( df : P -> A ) ( ds : P -> B ) ( x : P ) : Product A B := pair_Product A B ( df x ) ( ds x ).
(* from: originally defined by Hexirp *)

(** 直積型の余場合分けです。 *)

Definition identity_comatching_Product@{ i j | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( P : Type@{ j } ) ( codisplay : Product A B -> P ) ( df : P -> A ) ( idf : forall x : Product A B, Path A ( df ( codisplay x ) ) ( first_Product A B x ) ) ( ds : P -> B ) ( ids : forall x : Product A B, Path B ( ds ( codisplay x ) ) ( second_Product A B x ) ) ( x : Product A B ) : Path ( Product A B ) ( comatching_Product A B P df ds ( codisplay x ) ) x.
Proof.
  refine ( dependent_matching_Product A B ( fun x_ : Product A B => Path ( Product A B ) ( comatching_Product A B P df ds ( codisplay x_ ) ) x_ ) _ x ).
  refine ( fun ( xf : A ) ( xs : B ) => _ ).
  refine ( from_path_dest_Product A B ( comatching_Product A B P df ds ( codisplay ( pair_Product A B xf xs ) ) ) ( pair_Product A B xf xs ) _ ).
  change ( path_dest_Product A B ( comatching_Product A B P df ds ( codisplay ( pair_Product A B xf xs ) ) ) ( pair_Product A B xf xs ) ).
  change ( Product ( Path A ( first_Product A B ( comatching_Product A B P df ds ( codisplay ( pair_Product A B xf xs ) ) ) ) ( first_Product A B ( pair_Product A B xf xs ) ) ) ( Path B ( second_Product A B ( comatching_Product A B P df ds ( codisplay ( pair_Product A B xf xs ) ) ) ) ( second_Product A B ( pair_Product A B xf xs ) ) ) ).
  change ( Product ( Path A ( df ( codisplay ( pair_Product A B xf xs ) ) ) xf ) ( Path B ( ds ( codisplay ( pair_Product A B xf xs ) ) ) xs ) ).
  refine ( pair_Product ( Path A ( df ( codisplay ( pair_Product A B xf xs ) ) ) xf ) ( Path B ( ds ( codisplay ( pair_Product A B xf xs ) ) ) xs ) _ _ ).
  -
    change ( Path A ( df ( codisplay ( pair_Product A B xf xs ) ) ) xf ).
    change ( Path A ( df ( codisplay ( pair_Product A B xf xs ) ) ) ( first_Product A B ( pair_Product A B xf xs ) ) ).
    exact ( idf ( pair_Product A B xf xs ) ).
  -
    change ( Path B ( ds ( codisplay ( pair_Product A B xf xs ) ) ) xs ).
    change ( Path B ( ds ( codisplay ( pair_Product A B xf xs ) ) ) ( second_Product A B ( pair_Product A B xf xs ) ) ).
    exact ( ids ( pair_Product A B xf xs ) ).
Defined.
(* from: originally defined by Hexirp *)

(** 直積型の余場合分けの恒等式です。 *)

Definition curry_Product@{ i | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( C : Type@{ i } ) ( f : Product A B -> C ) ( x : A ) ( y : B ) : C := f ( pair_Product A B x y ).
(* from: originally defined by Hexirp *)

(** 関数のカリー化です。 *)

Definition uncurry_Product@{ i | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( C : Type@{ i } ) ( f : A -> B -> C) ( x : Product A B ) : C := matching_Product A B C ( fun ( xf : A ) ( xs : B ) => f xf xs ) x.
(* from: originally defined by Hexirp *)

(** 関数の非カリー化です。 *)

Definition map_Product@{ i j | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( C : Type@{ j } ) ( D : Type@{ j } ) ( f : A -> C ) ( g : B -> D ) ( x : Product A B ) : Product C D := matching_Product A B ( Product C D ) ( fun ( xf : A ) ( xs : B ) => pair_Product C D ( f xf ) ( g xs ) ) x.
(* from: originally defined by Hexirp *)

(** 直積型の写像です。 *)
