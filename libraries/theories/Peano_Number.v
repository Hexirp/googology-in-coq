(** 自然数型に関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Path.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Path.

(** ライブラリを開きます。 *)

Inductive Peano_Number@{ i | } : Type@{ i } := zero_Peano_Number : Peano_Number | succ_Peano_Number : Peano_Number -> Peano_Number.
(* from: originally defined by Hexirp *)

(** 自然数型です。 *)

Definition matching_Peano_Number@{ i j | } ( P : Type@{ j } ) ( cz : P ) ( cs : Peano_Number@{ i } -> P ) ( x : Peano_Number@{ i } ) : P := match x with zero_Peano_Number => cz | succ_Peano_Number xp => cs xp end.
(* from: originally defined by Hexirp *)

(** 自然数型の場合分けです。 *)

Definition identity_matching_Peano_Number@{ i j | } ( P : Type@{ j } ) ( display : P -> Peano_Number@{ i } ) ( cz : P ) ( icz : Path Peano_Number@{ i } ( display cz ) zero_Peano_Number ) ( cs : Peano_Number@{ i } -> P ) ( ics : forall xp : Peano_Number@{ i }, Path Peano_Number@{ i } ( display ( cs xp ) ) ( succ_Peano_Number xp ) ) ( x : Peano_Number@{ i } ) : Path Peano_Number@{ i } ( display ( matching_Peano_Number P cz cs x ) ) x := match x as x_ return Path Peano_Number@{ i } ( display ( matching_Peano_Number P cz cs x_ ) ) x_ with zero_Peano_Number => icz | succ_Peano_Number xp => ics xp end.
(* from: originally defined by Hexirp *)

(** 自然数型の場合分けの恒等式です。 *)

Definition dependent_matching_Peano_Number@{ i j | } ( P : Peano_Number@{ i } -> Type@{ j } ) ( cz : P zero_Peano_Number ) ( cs : forall xp : Peano_Number@{ i }, P ( succ_Peano_Number xp ) ) ( x : Peano_Number@{ i } ) : P x := match x as x_ return P x_ with zero_Peano_Number => cz | succ_Peano_Number xp => cs xp end.
(* from: originally defined by Hexirp *)

(** 自然数型の場合分けです。 *)

Definition recursion_Peano_Number@{ i j | } ( P : Type@{ j } ) ( cz : P ) ( cs : P -> P ) ( x : Peano_Number@{ i } ) : P := ( fix rec ( x_ : Peano_Number@{ i } ) { struct x_ } : P := matching_Peano_Number P cz ( fun xp : Peano_Number@{ i } => cs ( rec xp ) ) x_ ) x.
(* from: originally defined by Hexirp *)

(** 自然数型の再帰です。 *)

Definition identity_recursion_Peano_Number@{ i j | } ( P : Type@{ j } ) ( display : P -> Peano_Number@{ i } ) ( cz : P ) ( icz : Path Peano_Number@{ i } ( display cz ) zero_Peano_Number ) ( cs : P -> P ) ( ics : forall ( xp : Peano_Number@{ i } ) ( rp : P ), Path Peano_Number@{ i } ( display rp ) xp -> Path Peano_Number@{ i } ( display ( cs rp ) ) ( succ_Peano_Number xp ) ) ( x : Peano_Number@{ i } ) : Path Peano_Number@{ i } ( display ( recursion_Peano_Number P cz cs x ) ) x.
Proof.
  exact _.
Defined.
(* from: originally defined by Hexirp *)

(** 自然数型の再帰の恒等式です。 *)
