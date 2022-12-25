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

Definition trpt_Path@{ i j | } ( A : Type@{ i } ) ( B : A -> Type@{ j } ) ( x : A ) ( y : A ) ( p : Path A x y ) ( u : B x ) : B y := matching_Path A x B u y p.
(* from: originally defined by Hexirp *)

(** 輸送です。 *)

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

Definition trpv_Path@{ i j | } ( A : Type@{ i } ) ( B : A -> Type@{ j } ) ( x : A ) ( y : A ) ( p : Path A x y ) ( u : B y ) : B x := trpt_Path A B y x ( inv_Path A x y p) u.
(* from: originally defined by Hexirp *)

(** 道による輸送と逆です。 *)

Definition conv_Path@{ i | } ( A : Type@{ i } ) ( x : A ) ( y : A ) ( z : A ) ( p : Path A x y ) ( q : Path A x z ) : Path A y z := conc_Path A y x z ( inv_Path A x y p ) q.
(* from: originally defined by Hexirp *)

(** 道の結合と逆です。 *)

Definition map_Path@{ i | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( f : A -> B ) ( x : A ) ( y : A ) ( p : Path A x y ) : Path B ( f x ) ( f y ) := ap_Path A B f x y p.
(* from: originally defined by Hexirp *)

(** 道から道への写像です。 *)

Definition comatching_Path@{ i j | } ( A : Type@{ i } ) ( a : A ) ( P : Type@{ j } ) ( display : P -> A ) ( x : P ) ( ix : Path A ( display x ) a ) : Path A a ( display x ) := inv_Path A ( display x ) a ix.
(* from: originally defined by Hexirp *)

(** 道の余場合分けです。 *)

Fail Definition identity_comatching_Path@{ i j | } ( A : Type@{ i } ) ( a : A ) ( P : Type@{ j } ) ( display : P -> A ) ( codisplay : forall a' : A, Path A a a' -> P ) ( identity_codisplay : forall ( a' : A ) ( x : Path A a a' ), Path A ( display ( codisplay a' x ) ) a' ) ( a' : A ) ( x : Path A a a' ) : Path ( Path A a a' ) ( conc_Path A a ( display ( codisplay a' x ) ) a' ( comatching_Path A a P display ( codisplay a' x ) ( conc_Path A ( display ( codisplay a' x ) ) a' a ( identity_codisplay a' x ) ( inv_Path A a a' x ) ) ) ( identity_codisplay a' x ) ) x := match x as x_ in Path _ _ a'_ return Path ( Path A a a'_ ) ( conc_Path A a ( display ( codisplay a'_ x_ ) ) a'_ ( comatching_Path A a P display ( codisplay a'_ x_ ) ( conc_Path A ( display ( codisplay a'_ x_ ) ) a'_ a ( identity_codisplay a'_ x_ ) ( inv_Path A a a'_ x_ ) ) ) ( identity_codisplay a'_ x_ ) ) x_ with id_Path _ _ => _ end.
(* from: originally defined by Hexirp *)

(** 道の余場合分けの恒等式です。たぶん証明できると思いますが、グルーポイドの計算が必要になるので、いったん飛ばします。 *)

(** ** 応用 *)

Definition trpt_2_Path@{ i j | } ( A : Type@{ i } ) ( xa : A ) ( ya : A ) ( B : Type@{ i } ) ( xb : B ) ( yb : B ) ( C : A -> B -> Type@{ j } ) ( pa : Path A xa ya ) ( pb : Path B xb yb ) ( u : C xa xb ) : C ya yb := trpt_Path B ( C ya ) xb yb pb ( trpt_Path A ( fun ya_ : A => C ya_ xb ) xa ya pa u ).
(* from: originally defined by Hexirp *)

(** 二つの道を通した輸送です。 *)
