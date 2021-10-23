(** 点ごとの道です。 *)

Require Googology_In_Coq.Base.Base.
Require Googology_In_Coq.Base.Path.
Require Googology_In_Coq.Base.Negation.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を開きます。 *)

Definition T {A : Type} (x : A) (y : A) : Type
  := Negation.T (Path.T x y)
.
(* from: originally defined by Hexirp *)

(** 主型です。 *)

Definition symmetry {A : Type} {x : A} {y : A}
  : T x y -> T y x
  := fun (npxy : T x y) (pyx : Path.T y x) => npxy (Path.inv pyx)
.
(* from: originally defined by Hexirp *)

(** 対称律です。 *)
