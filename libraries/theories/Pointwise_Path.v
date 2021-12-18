(** 点ごとの道のモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Dependent_Function.
Require Googology_In_Coq.Function.
Require Googology_In_Coq.Path.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Dependent_Function (Dependent_Function).
Import Googology_In_Coq.Function (Function).
Import Googology_In_Coq.Path (Path).

(** ライブラリを開きます。 *)

Definition
  Pointwise_Path@{i | } (A : Type@{i}) (B : A -> Type@{i})
    : Dependent_Function A B -> Dependent_Function A B -> Type@{i}
    :=
      fun (f : Dependent_Function A B) (g : Dependent_Function A B) =>
        forall x : A, Path (f x) (g x)
.
(* from: originally defined by Hexirp *)

(** 点ごとの道です。 *)

Definition
  Pointwise_Path_Nodep@{i | } (A : Type@{i}) (B : Type@{i})
    : Function A B -> Function A B -> Type@{i}
    :=
      fun (f : Function A B) (g : Function A B) =>
        forall x : A, Path (f x) (g x)
.
(* from: originally defined by Hexirp *)

(** 点ごとの道です。 *)

Definition
  apply@{i | }
      {A : Type@{i}}
      {B : A -> Type@{i}}
      {f : Dependent_Function A B}
      {g : Dependent_Function A B}
    : Pointwise_Path A B f g -> forall x : A, Path (f x) (g x)
    := fun (p : Pointwise_Path A B f g) (x : A) => p x
.
(* from: originally defined by Hexirp *)

(** 点ごとの道を一点で具体化します。 *)

Definition
  id@{i | } {A : Type@{i}} {B : A -> Type@{i}} {f : Dependent_Function A B}
    : Pointwise_Path A B f f
    := fun x : A => Path.id (f x)
.
(* from: originally defined by Hexirp *)

(** 点ごとの恒等道です。 *)

Definition
  conc@{i | }
      {A : Type@{i}}
      {B : A -> Type@{i}}
      {f : Dependent_Function A B}
      {g : Dependent_Function A B}
      {h : Dependent_Function A B}
    :
        Pointwise_Path A B f g
      ->
        Pointwise_Path A B g h
      ->
        Pointwise_Path A B f h
    :=
      fun (p : Pointwise_Path A B f g) (q : Pointwise_Path A B g h) =>
        fun x : A => conc (p x) (q x)
.
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
