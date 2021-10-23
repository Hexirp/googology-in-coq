(** 点ごとの道です。 *)

Require Googology_In_Coq.Base.Base.
Require Googology_In_Coq.Base.Function.
Require Googology_In_Coq.Base.Path.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を開きます。 *)

Definition T {A : Type} {B : Type}
  : (A -> B) -> (A -> B) -> Type
  :=
    fun (f : A -> B) (g : A -> B) =>
      forall x : A, Path.T (f x) (g x)
.
(* from: originally defined by Hexirp *)

(** 主型です。 *)

Definition apply {A : Type} {B : Type} {f : A -> B} {g : A -> B}
  : T f g -> forall x : A, Path.T (f x) (g x)
  := fun (p : T f g) (x : A) => p x
.
(* from: originally defined by Hexirp *)

(** 点ごとの道を一点で具体化します。 *)

Definition id {A : Type} {B : Type} {f : A -> B}
  : T f f
  := fun x : A => Path.id
.
(* from: originally defined by Hexirp *)

(** 点ごとの道の恒等道です。 *)

Definition conc
    {A : Type}
    {B : Type}
    {f : A -> B}
    {g : A -> B}
    {h : A -> B}
  : T f g -> T g h -> T f h
.
Proof.
  unfold T.
  move=> p q.
  move=> x.
  exact (Path.conc (p x) (q x)).
Defined.
(* from: originally defined by Hexirp *)

(** 点ごとの道の合成です。 *)

Definition inv
    {A : Type}
    {B : Type}
    {f : A -> B}
    {g : A -> B}
  : T f g -> T g f
.
Proof.
  unfold T.
  move=> p.
  move=> x.
  exact (Path.inv (p x)).
Defined.
(* from: originally defined by Hexirp *)

(** 点ごとの道の逆です。 *)

Definition wisker_L
    {A : Type}
    {B : Type}
    {C : Type}
    (f : B -> C)
    {g : A -> B}
    {h : A -> B}
  : T g h -> T (Function.comp f g) (Function.comp f h)
.
Proof.
  unfold T.
  move=> p.
  move=> x.
  exact (Path.ap f (p x)).
Defined.
(* from: originally defined by Hexirp *)

(** 左からの髭つけです。 *)

Definition wisker_R
    {A : Type}
    {B : Type}
    {C : Type}
    (f : A -> B)
    {g : B -> C}
    {h : B -> C}
  : T g h -> T (Function.comp g f) (Function.comp h f)
.
Proof.
  unfold T.
  move=> p.
  move=> x.
  exact (p (f x)).
Defined.
(* from: originally defined by Hexirp *)

(** 右からの髭つけです。 *)

Definition wisker_L_R
    {A : Type}
    {B : Type}
    {C : Type}
    {D : Type}
    (f_0 : C -> D)
    (f_1 : A -> B)
    {g : B -> C}
    {h : B -> C}
  :
      T g h
    ->
      T
        (Function.comp f_0 (Function.comp g f_1))
        (Function.comp f_0 (Function.comp h f_1))
  := fun p : T g h => wisker_L f_0 (wisker_R f_1 p)
.
(* from: originally defined by Hexirp *)

(** 左右からの髭つけです。 *)
