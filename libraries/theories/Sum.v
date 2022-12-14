(** 直和型に関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Path.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Path.

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

Definition map_Sum@{ i | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( C : Type@{ i } ) ( D : Type@{ i } ) ( f : A -> C ) ( g : B -> D ) : Sum A B -> Sum C D := matching_Sum A B ( Sum C D ) ( fun xl : A => left_Sum C D ( f xl ) ) ( fun xr : B => right_Sum C D ( g xr ) ).
(* from: originally defined by Hexirp *)

(** 直和型の写像です。 *)
