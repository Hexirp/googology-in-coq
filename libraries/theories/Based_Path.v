(** 基点付き道に関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Path.
Require Googology_In_Coq.Dependent_Sum.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Path.
Import Googology_In_Coq.Dependent_Sum.

(** ライブラリを開きます。 *)

Definition Based_Path@{ i | } ( A : Type@{ i } ) ( a : A ) : Type@{ i } := Dependent_Sum A ( fun a' : A => Path A a a' ).
(* from: originally defined by Hexirp *)

(** 基点付き道の型です。 *)

Definition id_Based_Path@{ i | } ( A : Type@{ i } ) ( a : A ) : Based_Path A a := pair_Dependent_Sum A ( fun a' : A => Path A a a' ) a ( id_Path A a ).
(* from: originally defined by Hexirp *)

(** 基点付き恒等道です。 *)

Definition matching_Based_Path@{ i | } ( A : Type@{ i } ) ( a : A ) ( P : Type@{ i } ) ( ci : P ) ( x : Based_Path A a ) : P := matching_Dependent_Sum A ( fun a' : A => Path A a a' ) P ( fun ( a' : A ) ( p : Path A a a' ) => matching_Path A a ( fun a'_ : A => P ) ci a' p ) x.
(* from: originally defined by Hexirp *)

(** 基点付き道の型の場合分けです。 *)

Definition identity_matching_Based_Path@{ i | } ( A : Type@{ i } ) ( a : A ) ( P : Type@{ i } ) ( display : P -> Based_Path A a ) ( ci : P ) ( ici : Path ( Based_Path A a ) ( display ci ) ( id_Based_Path A a ) ) ( x : Based_Path A a ) : Path ( Based_Path A a ) ( display ( matching_Based_Path A a P ci x ) ) x.
Proof.
  refine ( dependent_matching_Dependent_Sum A ( fun a' : A => Path A a a' ) ( fun x_ : Dependent_Sum A ( fun a' : A => Path A a a' ) => Path ( Based_Path A a ) ( display ( matching_Based_Path A a P ci x_ ) ) x_ ) _ x ).
  refine ( fun ( a' : A ) ( p : Path A a a' ) => _ ).
  change ( Path ( Based_Path A a ) ( display ( matching_Based_Path A a P ci ( pair_Dependent_Sum A ( fun a' : A => Path A a a' ) a' p ) ) ) ( pair_Dependent_Sum A ( fun a' : A => Path A a a' ) a' p ) ).
  refine ( dependent_matching_Path A a ( fun ( a'_ : A ) ( p_ : Path A a a'_ ) => Path ( Based_Path A a ) ( display ( matching_Based_Path A a P ci ( pair_Dependent_Sum A ( fun a' : A => Path A a a' ) a'_ p_ ) ) ) ( pair_Dependent_Sum A ( fun a' : A => Path A a a' ) a'_ p_ ) ) _ a' p ).
  change ( Path ( Based_Path A a ) ( display ( matching_Based_Path A a P ci ( pair_Dependent_Sum A ( fun a' : A => Path A a a' ) a ( id_Path A a ) ) ) ) ( pair_Dependent_Sum A ( fun a' : A => Path A a a' ) a ( id_Path A a ) ) ).
  change ( Path ( Based_Path A a ) ( display ci ) ( pair_Dependent_Sum A ( fun a' : A => Path A a a' ) a ( id_Path A a ) ) ).
  change ( Path ( Based_Path A a ) ( display ci ) ( id_Based_Path A a ) ).
  exact ici.
Defined.
(* from: originally defined by Hexirp *)

(** 基点付き道の型の場合分けの恒等式です。 *)

Definition dependent_matching_Based_Path@{ i | } ( A : Type@{ i } ) ( a : A ) ( P : Based_Path A a -> Type@{ i } ) ( ci : P ( id_Based_Path A a ) ) ( x : Based_Path A a ) : P x := dependent_matching_Dependent_Sum A ( fun a' : A => Path A a a' ) ( fun x_ : Dependent_Sum A ( fun a' : A => Path A a a' ) => P x_ ) ( fun ( a' : A ) ( p : Path A a a' ) => dependent_matching_Path A a ( fun ( a'_ : A ) ( p_ : Path A a a'_ ) => P ( pair_Dependent_Sum A ( fun a' : A => Path A a a' ) a'_ p_ ) ) ci a' p ) x.
(* from: originally defined by Hexirp *)

(** 基点付き道の型の依存場合分けです。 *)
