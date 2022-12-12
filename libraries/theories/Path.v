(** 道に関するモジュールです。 *)

Require Googology_In_Coq.Base.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.

(** ライブラリを開きます。 *)

Inductive Path@{ i | } ( A : Type@{ i } ) ( a : A ) : A -> Type@{ i } := id_Path : Path A a a.

(** 道の型です。 *)

Definition matching_Path@{ i j | } ( A : Type@{ i } ) ( a : A ) ( P : A -> Type@{ j } ) ( ci : P a ) ( a' : A ) ( x : Path A a a' ) : P a' := match x in Path _ _ a'_ return P a'_ with id_Path _ _ => ci end.

(** 道の場合分けです。 *)

Definition identity_matching_Path@{ i j | } ( A : Type@{ i } ) ( a : A ) ( P : A -> Type@{ j } ) ( display : forall a' : A, P a' -> Path A a a' ) ( ci : P a ) ( ici : Path ( Path A a a ) ( display a ci ) ( id_Path A a ) ) ( a' : A ) ( x : Path A a a' ) : Path ( Path A a a' ) ( display a' ( matching_Path A a P ci a' x ) ) x := match x as x_ in Path _ _ a'_ return Path ( Path A a a'_ ) ( display a'_ ( matching_Path A a P ci a'_ x_ ) ) x_ with id_Path _ _ => ici end.

(** 道の場合分けの恒等式です。 *)

Definition trpt_Path@{ i j | } ( A : Type@{ i } ) ( x : A ) ( y : A ) ( B : A -> Type@{ j } ) ( p : Path A x y ) ( u : B x ) : B y := matching_Path A x B u y p.
(* from: originally defined by Hexirp *)

(** 輸送です。 *)

Definition conc_Path@{ i | } ( A : Type@{ i } ) ( x : A ) ( y : A ) ( z : A ) ( p : Path A x y ) ( q : Path A y z ) : Path A x z := trpt_Path A y z ( Path A x ) q p.
(* from: originally defined by Hexirp *)

(** 道の結合です。 *)

Definition inv_Path@{ i | } ( A : Type@{ i } ) ( x : A ) ( y : A ) ( p : Path A x y ) : Path A y x := trpt_Path A x y ( fun y_ : A => Path A y_ x ) p ( id_Path A x ).
(* from: originally defined by Hexirp *)

(** 道の逆です。 *)

Definition ap_Path@{ i | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( f : A -> B ) ( x : A ) ( y : A ) ( p : Path A x y ) : Path B ( f x ) ( f y ) := trpt_Path A x y ( fun y_ : A => Path B ( f x ) ( f y_ ) ) p ( id_Path B ( f x ) ).
(* from: originally defined by Hexirp *)

(** 道への適用です。 *)

Definition trpv_Path@{ i | } ( A : Type@{ i } ) ( x : A ) ( y : A ) ( B : A -> Type@{ i } ) ( p : Path A x y ) ( u : B y ) : B x := trpt_Path A y x B ( inv_Path A x y p)  u.
(* from: originally defined by Hexirp *)

(** 道による輸送と逆です。 *)

Definition conv_Path@{ i | } ( A : Type@{ i } ) ( x : A ) ( y : A ) ( z : A ) ( p : Path A x y ) ( q : Path A x z ) : Path A y z := conc_Path A y x z ( inv_Path A x y p ) q.
(* from: originally defined by Hexirp *)

(** 道の結合と逆です。 *)

Definition map_Path@{ i | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( f : A -> B ) ( x : A ) ( y : A ) ( p : Path A x y ) : Path B ( f x ) ( f y ) := ap_Path A B f x y p.
(* from: originally defined by Hexirp *)

(** 道から道への写像です。 *)
