(** 自然数に関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Path.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Path.

(** ライブラリを開きます。 *)

Inductive Peano_Number@{ i | } : Type@{ i } := zero_Peano_Number : Peano_Number | succ_Peano_Number : Peano_Number -> Peano_Number.
(* from: originally defined by Hexirp *)

(** 自然数の型です。 *)

Definition matching_Peano_Number@{ i j | } ( P : Type@{ j } ) ( cz : P ) ( cs : Peano_Number@{ i } -> P ) ( x : Peano_Number@{ i } ) : P := match x with zero_Peano_Number => cz | succ_Peano_Number xp => cs xp end.
(* from: originally defined by Hexirp *)

(** 自然数の型の場合分けです。 *)

Definition identity_matching_Peano_Number@{ i j | } ( P : Type@{ j } ) ( display : P -> Peano_Number@{ i } ) ( cz : P ) ( icz : Path Peano_Number@{ i } ( display cz ) zero_Peano_Number ) ( cs : Peano_Number@{ i } -> P ) ( ics : forall xp : Peano_Number@{ i }, Path Peano_Number@{ i } ( display ( cs xp ) ) ( succ_Peano_Number xp ) ) ( x : Peano_Number@{ i } ) : Path Peano_Number@{ i } ( display ( matching_Peano_Number P cz cs x ) ) x := match x as x_ return Path Peano_Number@{ i } ( display ( matching_Peano_Number P cz cs x_ ) ) x_ with zero_Peano_Number => icz | succ_Peano_Number xp => ics xp end.
(* from: originally defined by Hexirp *)

(** 自然数の型の場合分けの恒等式です。 *)

Definition dependent_matching_Peano_Number@{ i j | } ( P : Peano_Number@{ i } -> Type@{ j } ) ( cz : P zero_Peano_Number ) ( cs : forall xp : Peano_Number@{ i }, P ( succ_Peano_Number xp ) ) ( x : Peano_Number@{ i } ) : P x := match x as x_ return P x_ with zero_Peano_Number => cz | succ_Peano_Number xp => cs xp end.
(* from: originally defined by Hexirp *)

(** 自然数の型の場合分けです。 *)

Definition recursion_Peano_Number@{ i j | } ( P : Type@{ j } ) ( cz : P ) ( cs : P -> P ) ( x : Peano_Number@{ i } ) : P := ( fix rec ( x_ : Peano_Number@{ i } ) { struct x_ } : P := match x_ with zero_Peano_Number => cz | succ_Peano_Number xp => cs ( rec xp ) end ) x.
(* from: originally defined by Hexirp *)

(** 自然数の型の再帰です。 *)

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

(** 自然数の型の再帰の恒等式です。 *)

Definition dependent_recursion_Peano_Number@{ i j | } ( P : Peano_Number@{ i } -> Type@{ j } ) ( cz : P zero_Peano_Number ) ( cs : forall xp : Peano_Number@{ i }, P xp -> P ( succ_Peano_Number xp ) ) ( x : Peano_Number@{ i } ) : P x := ( fix rec ( x_ : Peano_Number@{ i } ) { struct x_ } : P x_ := match x_ as x__ return P x__ with zero_Peano_Number => cz | succ_Peano_Number xp => cs xp ( rec xp ) end ) x.
(* from: originally defined by Hexirp *)

(** 自然数の型の依存再帰です。 *)

Definition one_Peano_Number@{ i | } : Peano_Number@{ i } := succ_Peano_Number zero_Peano_Number.
(* from: originally defined by Hexirp *)

(** 1 です。 *)

Definition two_Peano_Number@{ i | } : Peano_Number@{ i } := succ_Peano_Number one_Peano_Number.
(* from: originally defined by Hexirp *)

(** 2 です。 *)

Definition three_Peano_Number@{ i | } : Peano_Number@{ i } := succ_Peano_Number two_Peano_Number.
(* from: originally defined by Hexirp *)

(** 3 です。 *)

Definition four_Peano_Number@{ i | } : Peano_Number@{ i } := succ_Peano_Number three_Peano_Number.
(* from: originally defined by Hexirp *)

(** 4 です。 *)

Definition add_Peano_Number@{ i | } ( m : Peano_Number@{ i } ) ( n : Peano_Number@{ i } ) : Peano_Number@{ i } := recursion_Peano_Number Peano_Number@{ i } m ( fun rp : Peano_Number@{ i } => succ_Peano_Number rp ) n.
(* from: originally defined by Hexirp *)

(** 加算です。 *)

Definition left_unit_add_Peano_Number@{ i | } ( n : Peano_Number@{ i } ) : Path Peano_Number@{ i } ( add_Peano_Number zero_Peano_Number n ) n.
Proof.
  refine ( dependent_recursion_Peano_Number ( fun n_ : Peano_Number@{ i } => Path Peano_Number@{ i } ( add_Peano_Number zero_Peano_Number n_ ) n_ ) _ _ n ).
  -
    change ( Path Peano_Number@{ i } ( add_Peano_Number zero_Peano_Number zero_Peano_Number ) zero_Peano_Number ).
    change ( Path Peano_Number@{ i } zero_Peano_Number zero_Peano_Number ).
    exact ( id_Path Peano_Number@{ i } zero_Peano_Number ).
  -
    refine ( fun ( np : Peano_Number@{ i } ) ( rp : Path Peano_Number@{ i } ( add_Peano_Number zero_Peano_Number np ) np ) => _ ).
    change ( Path Peano_Number@{ i } ( add_Peano_Number zero_Peano_Number ( succ_Peano_Number np ) ) ( succ_Peano_Number np ) ).
    change ( Path Peano_Number@{ i } ( succ_Peano_Number ( add_Peano_Number zero_Peano_Number np ) ) ( succ_Peano_Number np ) ).
    exact ( ap_Path Peano_Number@{ i } Peano_Number@{ i } succ_Peano_Number ( add_Peano_Number zero_Peano_Number np ) np rp ).
Defined.
(* from: originally defined by Hexirp *)

(** 加算の左単位元法則です。 *)

Definition right_unit_add_Peano_Number@{ i | } ( m : Peano_Number@{ i } ) : Path Peano_Number@{ i } ( add_Peano_Number m zero_Peano_Number ) m := id_Path Peano_Number@{ i } ( add_Peano_Number m zero_Peano_Number ).
(* from: originally defined by Hexirp *)

(** 加算の右単位元法則です。 *)

Definition left_succ_add_Peano_Number@{ i | } ( m : Peano_Number@{ i } ) ( n : Peano_Number@{ i } ) : Path Peano_Number@{ i } ( add_Peano_Number ( succ_Peano_Number m ) n ) ( succ_Peano_Number ( add_Peano_Number m n ) ).
Proof.
  refine ( dependent_recursion_Peano_Number ( fun n_ : Peano_Number@{ i } => Path Peano_Number@{ i } ( add_Peano_Number ( succ_Peano_Number m ) n_ ) ( succ_Peano_Number ( add_Peano_Number m n_ ) ) ) _ _ n ).
  -
    change ( Path Peano_Number@{ i } ( add_Peano_Number ( succ_Peano_Number m ) zero_Peano_Number ) ( succ_Peano_Number ( add_Peano_Number m zero_Peano_Number ) ) ).
    change ( Path Peano_Number@{ i } ( succ_Peano_Number m ) ( succ_Peano_Number m ) ).
    exact ( id_Path Peano_Number@{ i } ( succ_Peano_Number m ) ).
  -
    refine ( fun ( np : Peano_Number@{ i } ) ( rp : Path Peano_Number@{ i } ( add_Peano_Number ( succ_Peano_Number m ) np ) ( succ_Peano_Number ( add_Peano_Number m np ) ) ) => _ ).
    change ( Path Peano_Number@{ i } ( add_Peano_Number ( succ_Peano_Number m ) ( succ_Peano_Number np ) ) ( succ_Peano_Number ( add_Peano_Number m ( succ_Peano_Number np ) ) ) ).
    change ( Path Peano_Number@{ i } ( succ_Peano_Number ( add_Peano_Number ( succ_Peano_Number m ) np ) ) ( succ_Peano_Number ( succ_Peano_Number ( add_Peano_Number m np ) ) ) ).
    exact ( ap_Path Peano_Number@{ i } Peano_Number@{ i } succ_Peano_Number ( add_Peano_Number ( succ_Peano_Number m ) np ) ( succ_Peano_Number ( add_Peano_Number m np ) ) rp ).
Defined.
(* from: originally defined by Hexirp *)

(** 加算の左に後者数が入る時の等式です。 *)

Definition right_succ_add_Peano_Number@{ i | } ( m : Peano_Number@{ i } ) ( n : Peano_Number@{ i } ) : Path Peano_Number@{ i } ( add_Peano_Number m ( succ_Peano_Number n ) ) ( succ_Peano_Number ( add_Peano_Number m n ) ) := id_Path Peano_Number@{ i } ( add_Peano_Number m ( succ_Peano_Number n ) ).
(* from: originally defined by Hexirp *)

(** 加算の右に後者数が入る時の等式です。 *)

Definition assoc_add_Peano_Number@{ i | } ( m : Peano_Number@{ i } ) ( n : Peano_Number@{ i } ) ( k : Peano_Number@{ i } ) : Path Peano_Number@{ i } ( add_Peano_Number ( add_Peano_Number m n ) k ) ( add_Peano_Number m ( add_Peano_Number n k ) ).
Proof.
  refine ( dependent_recursion_Peano_Number ( fun k_ : Peano_Number@{ i } => Path Peano_Number@{ i } ( add_Peano_Number ( add_Peano_Number m n ) k_ ) ( add_Peano_Number m ( add_Peano_Number n k_ ) ) ) _ _ k ).
  -
    refine ( conc_Path Peano_Number@{ i } ( add_Peano_Number ( add_Peano_Number m n ) zero_Peano_Number ) ( add_Peano_Number m n ) ( add_Peano_Number m ( add_Peano_Number n zero_Peano_Number ) ) _ _ ).
    +
      exact ( right_unit_add_Peano_Number ( add_Peano_Number m n ) ).
    +
      refine ( ap_Path Peano_Number@{ i } Peano_Number@{ i } ( fun x : Peano_Number@{ i } => add_Peano_Number m x ) n ( add_Peano_Number n zero_Peano_Number ) _ ).
      refine ( inv_Path Peano_Number@{ i } ( add_Peano_Number n zero_Peano_Number ) n _ ).
      exact ( right_unit_add_Peano_Number n ).
  -
    refine ( fun ( kp : Peano_Number@{ i } ) ( rp : Path Peano_Number@{ i } ( add_Peano_Number ( add_Peano_Number m n ) kp ) ( add_Peano_Number m ( add_Peano_Number n kp ) ) ) => _ ).
    refine ( chain_4_conc_Path Peano_Number@{ i } ( add_Peano_Number ( add_Peano_Number m n ) ( succ_Peano_Number kp ) ) ( succ_Peano_Number ( add_Peano_Number ( add_Peano_Number m n ) kp ) ) ( succ_Peano_Number ( add_Peano_Number m ( add_Peano_Number n kp ) ) ) ( add_Peano_Number m ( succ_Peano_Number ( add_Peano_Number n kp ) ) ) ( add_Peano_Number m ( add_Peano_Number n ( succ_Peano_Number kp ) ) ) _ _ _ _ ).
    +
      exact ( right_succ_add_Peano_Number ( add_Peano_Number m n ) kp ).
    +
      exact ( ap_Path Peano_Number@{ i } Peano_Number@{ i } succ_Peano_Number ( add_Peano_Number ( add_Peano_Number m n ) kp ) ( add_Peano_Number m ( add_Peano_Number n kp ) ) rp ).
    +
      exact ( inv_Path Peano_Number@{ i } ( add_Peano_Number m ( succ_Peano_Number ( add_Peano_Number n kp ) ) ) ( succ_Peano_Number ( add_Peano_Number m ( add_Peano_Number n kp ) ) ) ( right_succ_add_Peano_Number m ( add_Peano_Number n kp ) ) ).
    +
      refine ( ap_Path Peano_Number@{ i } Peano_Number@{ i } ( fun x : Peano_Number@{ i } => add_Peano_Number m x ) ( succ_Peano_Number ( add_Peano_Number n kp ) ) ( add_Peano_Number n ( succ_Peano_Number kp ) ) _ ).
      refine ( inv_Path Peano_Number@{ i } ( add_Peano_Number n ( succ_Peano_Number kp ) ) ( succ_Peano_Number ( add_Peano_Number n kp ) ) _ ).
      exact ( right_succ_add_Peano_Number n kp ).
Defined.
(* from: originally defined by Hexirp *)

(** 加算の結合法則です。 *)

Definition comm_add_Peano_Number@{ i | } ( m : Peano_Number@{ i } ) ( n : Peano_Number@{ i } ) : Path Peano_Number@{ i } ( add_Peano_Number n m ) ( add_Peano_Number m n ).
Proof.
  refine ( dependent_recursion_Peano_Number ( fun n_ : Peano_Number@{ i } => Path Peano_Number@{ i } ( add_Peano_Number n_ m ) ( add_Peano_Number m n_ ) ) _ _ n ).
  -
    refine ( conc_Path Peano_Number@{ i } ( add_Peano_Number zero_Peano_Number m ) m ( add_Peano_Number m zero_Peano_Number ) _ _ ).
    +
      exact ( left_unit_add_Peano_Number m ).
    +
      exact ( inv_Path Peano_Number@{ i } ( add_Peano_Number m zero_Peano_Number ) m ( right_unit_add_Peano_Number m ) ).
  -
    refine ( fun ( np : Peano_Number@{ i } ) ( rp : Path Peano_Number@{ i } ( add_Peano_Number np m ) ( add_Peano_Number m np ) ) => _ ).
    refine ( chain_3_conc_Path Peano_Number@{ i } ( add_Peano_Number ( succ_Peano_Number np ) m ) ( succ_Peano_Number ( add_Peano_Number np m ) ) ( succ_Peano_Number ( add_Peano_Number m np ) ) ( add_Peano_Number m ( succ_Peano_Number np ) ) _ _ _ ).
    +
      exact ( left_succ_add_Peano_Number np m ).
    +
      exact ( ap_Path Peano_Number@{ i } Peano_Number@{ i } succ_Peano_Number ( add_Peano_Number np m ) ( add_Peano_Number m np) rp ).
    +
      exact ( inv_Path Peano_Number@{ i } ( add_Peano_Number m ( succ_Peano_Number np ) ) ( succ_Peano_Number ( add_Peano_Number m np ) ) ( right_succ_add_Peano_Number m np ) ).
Defined.
(* from: originally defined by Hexirp *)

(** 加算の交換法則です。 *)

Definition mul_Peano_Number@{ i | } ( m : Peano_Number@{ i } ) ( n : Peano_Number@{ i } ) : Peano_Number@{ i } := recursion_Peano_Number Peano_Number@{ i } zero_Peano_Number ( fun rp : Peano_Number@{ i } => add_Peano_Number m rp ) n.
(* from: originally defined by Hexirp *)

(** 乗算です。 *)

Definition exp_Peano_Number@{ i | } ( m : Peano_Number@{ i } ) ( n : Peano_Number@{ i } ) : Peano_Number@{ i } := recursion_Peano_Number Peano_Number@{ i } ( succ_Peano_Number zero_Peano_Number ) ( fun rp : Peano_Number@{ i } => mul_Peano_Number m rp ) n.
(* from: originally defined by Hexirp *)

(** 冪乗です。 *)
