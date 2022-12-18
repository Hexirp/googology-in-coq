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

Definition matching_Product@{ i j | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( P : Type@{ j } ) ( cp : A -> B -> P ) ( x : Product A B ) : P := match x with pair_Product _ _ a b => cp a b end.
(* from: originally defined by Hexirp *)

(** 直積型の場合分けです。 *)

Definition identity_matching_Product@{ i j | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( P : Type@{ j } ) ( display : P -> Product A B ) (cp : A -> B -> P ) ( icp : forall ( a : A ) ( b : B ), Path ( Product A B ) ( display ( cp a b ) ) ( pair_Product A B a b ) ) ( x : Product A B ) : Path ( Product A B ) ( display ( matching_Product A B P cp x ) ) x := match x as x_ return Path ( Product A B ) ( display ( matching_Product A B P cp x_ ) ) x_ with pair_Product _ _ a b => icp a b end.
(* from: originally defined by Hexirp *)

(** 直積型の場合分けの恒等式です。 *)

Definition first_Product@{ i | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( x : Product A B ) : A := match x with pair_Product _ _ a _ => a end.
(* from: originally defined by Hexirp *)

(** 直積型の第一射影関数です。 *)

Definition second_Product@{ i | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( x : Product A B ) : B := match x with pair_Product _ _ _ b => b end.
(* from: originally defined by Hexirp *)

(** 直積型の第二射影関数です。 *)

Definition comatching_Product@{ i j | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( P : Type@{ j } ) ( df : P -> A ) ( ds : P -> B ) ( x : P ) : Product A B := pair_Product A B ( df x ) ( ds x ).
(* from: originally defined by Hexirp *)

(** 直積型の余場合分けです。 *)

Definition path_proj_Product@{ i | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( x : Product A B ) ( y : Product A B ) : Path A ( first_Product A B x ) ( first_Product A B y ) -> Path B ( second_Product A B x ) ( second_Product A B y ) -> Path ( Product A B ) x y := match x as x_ return Path A ( first_Product A B x_ ) ( first_Product A B y ) -> Path B ( second_Product A B x_ ) ( second_Product A B y ) -> Path ( Product A B ) x_ y with pair_Product _ _ xf xs => match y as y_ return Path A xf ( first_Product A B y_ ) -> Path B xs ( second_Product A B y_ ) -> Path ( Product A B ) ( pair_Product A B xf xs ) y_ with pair_Product _ _ yf ys => fun ( pf : Path A xf yf ) ( ps : Path B xs ys ) => trpt_2_Path A xf yf B xs ys ( fun ( yf_ : A ) ( ys_ : B ) => Path ( Product A B ) ( pair_Product A B xf xs ) ( pair_Product A B yf_ ys_ ) ) pf ps ( id_Path ( Product A B ) ( pair_Product A B xf xs ) ) end end.

Definition identity_comatching_Product@{ i j | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( P : Type@{ j } ) ( codisplay : Product A B -> P ) ( df : P -> A ) ( idf : forall x : Product A B, Path A ( df ( codisplay x ) ) ( first_Product A B x ) ) ( ds : P -> B ) ( ids : forall x : Product A B, Path B ( ds ( codisplay x ) ) ( second_Product A B x ) ) ( x : Product A B ) : Path ( Product A B ) ( comatching_Product A B P df ds ( codisplay x ) ) x := match x as x_ return Path ( Product A B ) ( comatching_Product A B P df ds ( codisplay x_ ) ) x_ with pair_Product _ _ xf xs => path_proj_Product A B ( comatching_Product A B P df ds ( codisplay ( pair_Product A B xf xs ) ) ) ( pair_Product A B xf xs ) ( idf ( pair_Product A B xf xs ) ) ( ids ( pair_Product A B xf xs ) ) end.
(* from: originally defined by Hexirp *)

(** 直積型の余場合分けの恒等式です。ただし、これを実装するためには直積型の η 規則が必要であるため、今は実装できません。 *)

Definition curry_Product@{ i | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( C : Type@{ i } ) ( f : Product A B -> C ) ( x : A ) ( y : B ) : C := f ( pair_Product A B x y ).
(* from: originally defined by Hexirp *)

(** 関数のカリー化です。 *)

Definition uncurry_Product@{ i | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( C : Type@{ i } ) ( f : A -> B -> C) ( x : Product A B ) : C := f ( first_Product A B x ) ( second_Product A B x ).
(* from: originally defined by Hexirp *)

(** 関数の非カリー化です。 *)

Definition map_Product@{ i | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( C : Type@{ i } ) ( D : Type@{ i } ) ( f : A -> C ) ( g : B -> D ) ( x : Product A B ) : Product@{i} C D := pair_Product C D ( f ( first_Product A B x ) ) ( g ( second_Product A B x ) )
.
(* from: originally defined by Hexirp *)

(** 直積型の写像です。 *)
