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

Definition recursion_Peano_Number@{ i j | } ( P : Type@{ j } ) ( cz : P ) ( cs : P -> P ) ( x : Peano_Number@{ i } ) : P := ( fix rec ( x_ : Peano_Number@{ i } ) { struct x_ } : P := match x_ with zero_Peano_Number => cz | succ_Peano_Number xp => cs ( rec xp ) end ) x.
(* from: originally defined by Hexirp *)

(** 自然数型の再帰です。 *)

Definition identity_recursion_Peano_Number@{ i j | } ( P : Type@{ j } ) ( display : P -> Peano_Number@{ i } ) ( cz : P ) ( icz : Path Peano_Number@{ i } ( display cz ) zero_Peano_Number ) ( cs : P -> P ) ( ics : forall ( xp : Peano_Number@{ i } ) ( rp : P ), Path Peano_Number@{ i } ( display rp ) xp -> Path Peano_Number@{ i } ( display ( cs rp ) ) ( succ_Peano_Number xp ) ) ( x : Peano_Number@{ i } ) : Path Peano_Number@{ i } ( display ( recursion_Peano_Number P cz cs x ) ) x.
Proof.
  refine ( _ x ).
  refine ( fix rec ( x_ : Peano_Number@{ i } ) { struct x_ } : Path Peano_Number@{ i } ( display ( recursion_Peano_Number P cz cs x_ ) ) x_ := _ ).
  refine ( match x_ as x__ return Path Peano_Number@{ i } ( display ( recursion_Peano_Number P cz cs x__ ) ) x__ with zero_Peano_Number => _ | succ_Peano_Number xp => _ end ).
  -
    change ( Path Peano_Number@{ i } ( display ( recursion_Peano_Number P cz cs zero_Peano_Number ) ) zero_Peano_Number ).
    change ( Path Peano_Number@{ i } ( display cz ) zero_Peano_Number ).
    exact icz.
  -
    change ( Path Peano_Number@{ i } ( display ( recursion_Peano_Number P cz cs ( succ_Peano_Number xp ) ) ) ( succ_Peano_Number xp ) ).
    change ( Path Peano_Number@{ i } ( display ( cs ( recursion_Peano_Number P cz cs xp ) ) ) ( succ_Peano_Number xp ) ).
    refine ( ics xp ( recursion_Peano_Number P cz cs xp ) _ ).
    exact ( rec xp ).
Defined.
(* from: originally defined by Hexirp *)

(** 自然数型の再帰の恒等式です。 *)

Definition dependent_recursion_Peano_Number@{ i j | } ( P : Peano_Number@{ i } -> Type@{ j } ) ( cz : P zero_Peano_Number ) ( cs : forall xp : Peano_Number@{ i }, P xp -> P ( succ_Peano_Number xp ) ) ( x : Peano_Number@{ i } ) : P x := ( fix rec ( x_ : Peano_Number@{ i } ) { struct x_ } : P x_ := match x_ as x__ return P x__ with zero_Peano_Number => cz | succ_Peano_Number xp => cs xp ( rec xp ) end ) x.
(* from: originally defined by Hexirp *)

(** 自然数型の依存再帰です。 *)

Definition add_Peano_Number@{ i | } ( m : Peano_Number@{ i } ) ( n : Peano_Number@{ i } ) : Peano_Number@{ i } := recursion_Peano_Number ( Peano_Number@{ i } -> Peano_Number@{ i } ) ( fun n_ : Peano_Number@{ i } => n_ ) ( fun ( rp : Peano_Number@{ i } -> Peano_Number@{ i } ) ( n_ : Peano_Number@{ i } ) => succ_Peano_Number ( rp n_ ) ) m n.
(* from: originally defined by Hexirp *)

(** 加算です。 *)
