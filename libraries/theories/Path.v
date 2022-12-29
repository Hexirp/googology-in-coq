(** 道に関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Function.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Function.

(** ライブラリを開きます。 *)

Inductive Path@{ i | } ( A : Type@{ i } ) ( a : A ) : A -> Type@{ i } := id_Path : Path A a a.
(* from: originally defined by Hexirp *)

(** 道の型です。 *)

Definition matching_Path@{ i j | } ( A : Type@{ i } ) ( a : A ) ( P : A -> Type@{ j } ) ( ci : P a ) ( a' : A ) ( x : Path A a a' ) : P a' := match x in Path _ _ a'_ return P a'_ with id_Path _ _ => ci end.
(* from: originally defined by Hexirp *)

(** 道の場合分けです。 *)

Definition identity_matching_Path@{ i j | } ( A : Type@{ i } ) ( a : A ) ( P : A -> Type@{ j } ) ( display : forall a' : A, P a' -> Path A a a' ) ( ci : P a ) ( ici : Path ( Path A a a ) ( display a ci ) ( id_Path A a ) ) ( a' : A ) ( x : Path A a a' ) : Path ( Path A a a' ) ( display a' ( matching_Path A a P ci a' x ) ) x := match x as x_ in Path _ _ a'_ return Path ( Path A a a'_ ) ( display a'_ ( matching_Path A a P ci a'_ x_ ) ) x_ with id_Path _ _ => ici end.
(* from: originally defined by Hexirp *)

(** 道の場合分けの恒等式です。 *)

Definition dependent_matching_Path@{ i j | } ( A : Type@{ i } ) ( a : A ) ( P : forall a' : A, Path A a a' -> Type@{ j } ) ( ci : P a ( id_Path A a ) ) ( a' : A ) ( x : Path A a a' ) : P a' x := match x as x_ in Path _ _ a'_ return P a'_ x_ with id_Path _ _ => ci end.
(* from: originally defined by Hexirp *)

(** 道の依存場合分けです。 *)

Definition conc_Path@{ i | } ( A : Type@{ i } ) ( x : A ) ( y : A ) ( z : A ) ( p : Path A x y ) ( q : Path A y z ) : Path A x z := matching_Path A x ( fun y_ : A => forall z_ : A, Path A y_ z_ -> Path A x z_ ) ( fun ( z_ : A ) ( q_ : Path A x z_ ) => q_ ) y p z q.
(* from: originally defined by Hexirp *)

(** 道の結合です。 *)

Definition inv_Path@{ i | } ( A : Type@{ i } ) ( x : A ) ( y : A ) ( p : Path A x y ) : Path A y x := matching_Path A x ( fun y_ : A => Path A y_ x ) ( id_Path A x ) y p.
(* from: originally defined by Hexirp *)

(** 道の逆です。 *)

Definition assoc_Path@{ i | } ( A : Type@{ i } ) ( x : A ) ( y : A ) ( z : A ) ( w : A ) ( p : Path A x y ) ( q : Path A y z ) ( r : Path A z w ) : Path ( Path A x w ) ( conc_Path A x z w ( conc_Path A x y z p q ) r ) ( conc_Path A x y w p ( conc_Path A y z w q r ) ) := dependent_matching_Path A x ( fun ( y_ : A ) ( p_ : Path A x y_ ) => forall ( z_ : A ) ( q_ : Path A y_ z_ ) ( w_ : A ) ( r_ : Path A z_ w_ ), Path ( Path A x w_ ) ( conc_Path A x z_ w_ ( conc_Path A x y_ z_ p_ q_ ) r_ ) ( conc_Path A x y_ w_ p_ ( conc_Path A y_ z_ w_ q_ r_ ) ) ) ( fun ( z_ : A ) ( q_ : Path A x z_ ) ( w_ : A ) ( r_ : Path A z_ w_ ) => id_Path ( Path A x w_ ) ( conc_Path A x z_ w_ q_ r_ ) ) y p z q w r.
(* from: originally defined by Hexirp *)

(** 道の結合法則の等式です。 *)

Definition left_unit_Path@{ i | } ( A : Type@{ i } ) ( x : A ) ( y : A ) ( p : Path A x y ) : Path ( Path A x y ) ( conc_Path A x x y ( id_Path A x ) p ) p := id_Path ( Path A x y ) p.
(* from: originally defined by Hexirp *)

(** 道の左単位元法則の等式です。 *)

Definition right_unit_Path@{ i | } ( A : Type@{ i } ) ( x : A ) ( y : A ) ( p : Path A x y ) : Path ( Path A x y ) ( conc_Path A x y y p ( id_Path A y ) ) p := dependent_matching_Path A x ( fun ( y_ : A ) ( p_ : Path A x y_ ) => Path ( Path A x y_ ) ( conc_Path A x y_ y_ p_ ( id_Path A y_ ) ) p_ ) ( id_Path ( Path A x x ) ( id_Path A x ) ) y p.
(* from: originally defined by Hexirp *)

(** 道の右単位元法則の等式です。 *)

Definition left_inv_Path@{ i | } ( A : Type@{ i } ) ( x : A ) ( y : A ) ( p : Path A x y ) : Path ( Path A y y ) ( conc_Path A y x y ( inv_Path A x y p ) p ) ( id_Path A y ) := dependent_matching_Path A x ( fun ( y_ : A ) ( p_ : Path A x y_ ) => Path ( Path A y_ y_ ) ( conc_Path A y_ x y_ ( inv_Path A x y_ p_ ) p_ ) ( id_Path A y_ ) ) ( id_Path ( Path A x x ) ( id_Path A x ) ) y p.
(* from: originally defined by Hexirp *)

(** 道の左逆元法則の等式です。 *)

Definition right_inv_Path@{ i | } ( A : Type@{ i } ) ( x : A ) ( y : A ) ( p : Path A x y ) : Path ( Path A x x ) ( conc_Path A x y x p ( inv_Path A x y p ) ) ( id_Path A x ) := dependent_matching_Path A x ( fun ( y_ : A ) ( p_ : Path A x y_ ) => Path ( Path A x x ) ( conc_Path A x y_ x p_ ( inv_Path A x y_ p_ ) ) ( id_Path A x ) ) ( id_Path ( Path A x x ) ( id_Path A x ) ) y p.
(* from: originally defined by Hexirp *)

(** 道の右逆元法則の等式です。 *)

Definition ap_Path@{ i j | } ( A : Type@{ i } ) ( B : Type@{ j } ) ( f : A -> B ) ( x : A ) ( y : A ) ( p : Path A x y ) : Path B ( f x ) ( f y ) := matching_Path A x ( fun y_ : A => Path B ( f x ) ( f y_ ) ) ( id_Path B ( f x ) ) y p.
(* from: originally defined by Hexirp *)

(** 関数を道に適用する演算子です。 *)

Definition ap_idf_Path@{ i | } ( A : Type@{ i } ) ( x : A ) ( y : A ) ( p : Path A x y ) : Path ( Path A x y ) ( ap_Path A A ( id_Function A ) x y p ) p := dependent_matching_Path A x ( fun ( y_ : A ) ( p_ : Path A x y_ ) => Path ( Path A x y_ ) ( ap_Path A A ( id_Function A ) x y_ p_ ) p_ ) ( id_Path ( Path A x x ) ( id_Path A x ) ) y p.
(* from: originally defined by Hexirp *)

(** [ap_Path] と [id_Function] の等式です。 *)

Definition ap_comp_Path@{ i j k | } ( A : Type@{ i } ) ( B : Type@{ j } ) ( C : Type@{ k } ) ( f : B -> C ) ( g : A -> B ) ( x : A ) ( y : A ) ( p : Path A x y ) : Path ( Path C ( f ( g x ) ) ( f ( g y ) ) ) ( ap_Path A C ( comp_Function A B C f g ) x y p ) ( ap_Path B C f ( g x ) ( g y ) ( ap_Path A B g x y p ) ) := dependent_matching_Path A x ( fun ( y_ : A ) ( p_ : Path A x y_ ) => Path ( Path C ( f ( g x ) ) ( f ( g y_ ) ) ) ( ap_Path A C ( comp_Function A B C f g ) x y_ p_ ) ( ap_Path B C f ( g x ) ( g y_ ) ( ap_Path A B g x y_ p_ ) ) ) ( id_Path ( Path C ( f ( g x ) ) ( f ( g x ) ) ) ( id_Path C ( f ( g x ) ) ) ) y p.
(* from: originally defined by Hexirp *)

(** [ap_Path] と [comp_Function] の等式です。 *)

Definition ap_idp_Path@{ i j | } ( A : Type@{ i } ) ( B : Type@{ j } ) ( f : A -> B ) ( x : A ) : Path ( Path B ( f x ) ( f x ) ) ( ap_Path A B f x x ( id_Path A x ) ) ( id_Path B ( f x ) ) := id_Path ( Path B ( f x ) ( f x ) ) ( id_Path B ( f x ) ).
(* from: originally defined by Hexirp *)

(** [ap_Path] と [id_Path] の等式です。 *)

Definition ap_conc_Path@{ i | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( f : A -> B ) ( x : A ) ( y : A ) ( z : A ) ( p : Path A x y ) ( q : Path A y z ) : Path ( Path B ( f x ) ( f z ) ) ( ap_Path A B f x z ( conc_Path A x y z p q ) ) ( conc_Path B ( f x ) ( f y ) ( f z ) ( ap_Path A B f x y p ) ( ap_Path A B f y z q ) ) := dependent_matching_Path A x ( fun ( y_ : A ) ( p_ : Path A x y_ ) => forall ( z_ : A ) ( q_ : Path A y_ z_ ), Path ( Path B ( f x ) ( f z_ ) ) ( ap_Path A B f x z_ ( conc_Path A x y_ z_ p_ q_ ) ) ( conc_Path B ( f x ) ( f y_ ) ( f z_ ) ( ap_Path A B f x y_ p_ ) ( ap_Path A B f y_ z_ q_ ) ) ) ( fun ( z_ : A ) ( q_ : Path A x z_ ) => id_Path ( Path B ( f x ) ( f z_ ) ) ( ap_Path A B f x z_ q_ ) ) y p z q.
(* from: originally defined by Hexirp *)

(** [ap_Path] と [conc_Path] の等式です。 *)

Definition ap_inv_Path@{ i j | } ( A : Type@{ i } ) ( B : Type@{ j } ) ( f : A -> B ) ( x : A ) ( y : A ) ( p : Path A x y ) : Path ( Path B ( f y ) ( f x ) ) ( ap_Path A B f y x ( inv_Path A x y p ) ) ( inv_Path B ( f x ) ( f y ) ( ap_Path A B f x y p ) ) := dependent_matching_Path A x ( fun ( y_ : A ) ( p_ : Path A x y_ ) => Path ( Path B ( f y_ ) ( f x ) ) ( ap_Path A B f y_ x ( inv_Path A x y_ p_ ) ) ( inv_Path B ( f x ) ( f y_ ) ( ap_Path A B f x y_ p_ ) ) ) ( id_Path ( Path B ( f x ) ( f x ) ) ( id_Path B ( f x ) ) ) y p.
(* from: originally defined by Hexirp *)

(** [ap_Path] と [id_Path] の等式です。 *)

Definition trpt_Path@{ i j | } ( A : Type@{ i } ) ( B : A -> Type@{ j } ) ( x : A ) ( y : A ) ( p : Path A x y ) ( u : B x ) : B y := matching_Path A x ( fun y_ : A => B x -> B y_ ) ( id_Function ( B x ) ) y p u.
(* from: originally defined by Hexirp *)

(** 輸送です。 *)

Definition apd_Path@{ i j | } ( A : Type@{ i } ) ( B : A -> Type@{ j } ) ( f : forall a : A, B a ) ( x : A ) ( y : A ) ( p : Path A x y ) : Path ( B y ) ( trpt_Path A B x y p ( f x ) ) ( f y ) := dependent_matching_Path A x ( fun ( y_ : A ) ( p_ : Path A x y_ ) => Path ( B y_ ) ( trpt_Path A B x y_ p_ ( f x ) ) ( f y_ ) ) ( id_Path ( B x ) ( f x ) ) y p.
(* from: originally defined by Hexirp *)

(** 依存関数を道に適用する演算子です。 *)

Definition map_Path@{ i | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( f : A -> B ) ( x : A ) ( y : A ) ( p : Path A x y ) : Path B ( f x ) ( f y ) := ap_Path A B f x y p.
(* from: originally defined by Hexirp *)

(** 道から道への写像です。 *)

Definition comatching_Path@{ i j | } ( A : Type@{ i } ) ( a : A ) ( P : Type@{ j } ) ( display : P -> A ) ( x : P ) ( ix : Path A ( display x ) a ) : Path A a ( display x ) := inv_Path A ( display x ) a ix.
(* from: originally defined by Hexirp *)

(** 道の余場合分けです。 *)

Definition identity_comatching_Path@{ i j | } ( A : Type@{ i } ) ( a : A ) ( P : Type@{ j } ) ( display : P -> A ) ( codisplay : forall a' : A, Path A a a' -> P ) ( identity_codisplay : forall ( a' : A ) ( x : Path A a a' ), Path A ( display ( codisplay a' x ) ) a' ) ( a' : A ) ( x : Path A a a' ) : Path ( Path A a a' ) ( trpt_Path A ( fun a'_ : A => Path A a a'_ ) ( display ( codisplay a' x ) ) a' ( identity_codisplay a' x ) ( comatching_Path A a P display ( codisplay a' x ) ( trpt_Path A ( fun a_ : A => Path A ( display ( codisplay a' x ) ) a_ ) a' a ( inv_Path A a a' x ) ( identity_codisplay a' x ) ) ) ) x.
Proof.
  refine ( dependent_matching_Path A a ( fun ( a'_ : A ) ( x_ : Path A a a'_ ) => Path ( Path A a a'_ ) ( trpt_Path A ( fun a'_ : A => Path A a a'_ ) ( display ( codisplay a'_ x_ ) ) a'_ ( identity_codisplay a'_ x_ ) ( comatching_Path A a P display ( codisplay a'_ x_ ) ( trpt_Path A ( fun a_ : A => Path A ( display ( codisplay a'_ x_ ) ) a_ ) a'_ a ( inv_Path A a a'_ x_ ) ( identity_codisplay a'_ x_ ) ) ) ) x_ ) _ a' x ).
  change ( Path ( Path A a a ) ( trpt_Path A ( fun a'_ : A => Path A a a'_ ) ( display ( codisplay a ( id_Path A a ) ) ) a ( identity_codisplay a ( id_Path A a ) ) ( comatching_Path A a P display ( codisplay a ( id_Path A a ) ) ( trpt_Path A ( fun a_ : A => Path A ( display ( codisplay a ( id_Path A a ) ) ) a_ ) a a ( inv_Path A a a ( id_Path A a ) ) ( identity_codisplay a ( id_Path A a ) ) ) ) ) ( id_Path A a ) ).
  change ( Path ( Path A a a ) ( trpt_Path A ( fun a_ : A => Path A a a_ ) ( display ( codisplay a ( id_Path A a ) ) ) a ( identity_codisplay a ( id_Path A a ) ) ( comatching_Path A a P display ( codisplay a ( id_Path A a ) ) ( trpt_Path A ( fun a_ : A => Path A ( display ( codisplay a ( id_Path A a ) ) ) a_ ) a a ( inv_Path A a a ( id_Path A a ) ) ( identity_codisplay a ( id_Path A a ) ) ) ) ) ( id_Path A a ) ).
  change ( Path ( Path A a a ) ( trpt_Path A ( fun a_ : A => Path A a a_ ) ( display ( codisplay a ( id_Path A a ) ) ) a ( identity_codisplay a ( id_Path A a ) ) ( inv_Path A ( display ( codisplay a ( id_Path A a ) ) ) a ( trpt_Path A ( fun a_ : A => Path A ( display ( codisplay a ( id_Path A a ) ) ) a_ ) a a ( inv_Path A a a ( id_Path A a ) ) ( identity_codisplay a ( id_Path A a ) ) ) ) ) ( id_Path A a ) ).
  refine ( dependent_matching_Path A ( display ( codisplay a ( id_Path A a ) ) ) ( fun ( a__ : A ) ( i_ : Path A ( display ( codisplay a ( id_Path A a ) ) ) a__ ) => Path ( Path A a__ a__ ) ( trpt_Path A ( fun a_ : A => Path A a__ a_ ) ( display ( codisplay a ( id_Path A a ) ) ) a__ i_ ( inv_Path A ( display ( codisplay a ( id_Path A a ) ) ) a__ ( trpt_Path A ( fun a_ : A => Path A ( display ( codisplay a ( id_Path A a ) ) ) a_ ) a__ a__ ( inv_Path A a__ a__ ( id_Path A a__ ) ) i_ ) ) ) ( id_Path A a__ ) ) _ a ( identity_codisplay a ( id_Path A a ) ) ).
  change ( Path ( Path A ( display ( codisplay a ( id_Path A a ) ) ) ( display ( codisplay a ( id_Path A a ) ) ) ) ( trpt_Path A ( fun a_ : A => Path A ( display ( codisplay a ( id_Path A a ) ) ) a_ ) ( display ( codisplay a ( id_Path A a ) ) ) ( display ( codisplay a ( id_Path A a ) ) ) ( id_Path A ( display ( codisplay a ( id_Path A a ) ) ) ) ( inv_Path A ( display ( codisplay a ( id_Path A a ) ) ) ( display ( codisplay a ( id_Path A a ) ) ) ( trpt_Path A ( fun a_ : A => Path A ( display ( codisplay a ( id_Path A a ) ) ) a_ ) ( display ( codisplay a ( id_Path A a ) ) ) ( display ( codisplay a ( id_Path A a ) ) ) ( inv_Path A ( display ( codisplay a ( id_Path A a ) ) ) ( display ( codisplay a ( id_Path A a ) ) ) ( id_Path A ( display ( codisplay a ( id_Path A a ) ) ) ) ) ( id_Path A ( display ( codisplay a ( id_Path A a ) ) ) ) ) ) ) ( id_Path A ( display ( codisplay a ( id_Path A a ) ) ) ) ).
  exact ( id_Path ( Path A ( display ( codisplay a ( id_Path A a ) ) ) ( display ( codisplay a ( id_Path A a ) ) ) ) ( id_Path A ( display ( codisplay a ( id_Path A a ) ) ) ) ).
Defined.
(* from: originally defined by Hexirp *)

(** 道の余場合分けの恒等式です。 *)

(** ** 多重引数 *)

Definition trpt_2_Path@{ i j | } ( A : Type@{ i } ) ( B : Type@{ j } ) ( C : A -> B -> Type@{ j } ) ( xa : A ) ( ya : A ) ( pa : Path A xa ya ) ( xb : B ) ( yb : B ) ( pb : Path B xb yb ) ( u : C xa xb ) : C ya yb := matching_Path A xa ( fun ya_ : A => forall ( yb_ : B ) ( pb_ : Path B xb yb_ ), C ya_ yb_ ) ( fun ( yb_ : B ) ( pb_ : Path B xb yb_ ) => matching_Path B xb ( fun yb__ : B => C xa yb__ ) u yb_ pb_ ) ya pa yb pb.
(* from: originally defined by Hexirp *)

(** 二つの道を通した輸送です。 *)
