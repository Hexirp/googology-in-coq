(** 単一型に関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Path.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Path.

(** ライブラリを開きます。 *)

Inductive Unit@{ i | } : Type@{ i } := unit_Unit : Unit.
(* from: originally defined by Hexirp *)

(** 単一型です。 *)

Definition matching_Unit@{ i j | } ( P : Type@{ j } ) ( cu : P ) ( x : Unit@{ i } ) : P := match x with unit_Unit => cu end.
(* from: originally defined by Hexirp *)

(** 単一型の場合分けです。 *)

Definition identity_matching_Unit@{ i j | } ( P : Type@{ j } ) ( display : P -> Unit@{ i } ) ( cu : P ) ( icu : Path Unit@{ i } ( display cu ) unit_Unit ) ( x : Unit@{ i } ) : Path Unit@{ i } ( display ( matching_Unit P cu x ) ) x := match x as x_ return Path Unit ( display ( matching_Unit P cu x_ ) ) x_ with unit_Unit => icu end.
(* from: originally defined by Hexirp *)

(** 単一型の場合分けの恒等式です。 *)

Definition dependent_matching_Unit@{ i j | } ( P : Unit@{ i } -> Type@{ j } ) ( cu : P unit_Unit ) ( x : Unit@{ i } ) : P x := match x as x_ return P x_ with unit_Unit => cu end.
(* from: originally defined by Hexirp *)

(** 単一型の依存場合分けです。 *)

Definition from_path_cons_Unit@{ i | } ( x : Unit@{ i } ) ( y : Unit@{ i } ) : Path Unit@{ i } x y := dependent_matching_Unit ( fun x_ : Unit@{i} => forall y_ : Unit@{ i }, Path Unit@{ i } x_ y_ ) ( fun y_ : Unit@{ i } => dependent_matching_Unit ( fun y__ : Unit@{ i } => Path Unit@{ i } unit_Unit y__ ) ( id_Path Unit@{ i } unit_Unit ) y_ ) x y.
(* from: originally defined by Hexirp *)

(** 単一型の構築子の道から単一型の道を作る関数です。 *)

Definition comatching_Unit@{ i j | } ( P : Type@{ j } ) ( x : P ) : Unit@{ i } := unit_Unit.
(* from: originally defined by Hexirp *)

(** 単一型の余場合分けです。 *)

Definition identity_comatching_Unit@{ i j | } ( P : Type@{ j } ) ( codisplay : Unit@{ i } -> P ) ( x : Unit@{ i } ) : Path Unit@{ i } ( comatching_Unit P ( codisplay x ) ) x := dependent_matching_Unit ( fun x_ : Unit@{ i } => Path Unit@{ i } ( comatching_Unit P ( codisplay x_ ) ) x_ ) ( id_Path Unit@{ i } unit_Unit ) x.
(* from: originally defined by Hexirp *)

(** 単一型の余場合分けの恒等式です。 *)

Definition const_Unit@{ i j | } ( A : Type@{ j } ) : A -> Unit@{ i } := fun x : A => unit_Unit.
(* from: originally defined by Hexirp *)

(** 単一型の定数関数です。 *)
