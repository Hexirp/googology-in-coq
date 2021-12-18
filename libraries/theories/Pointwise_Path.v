(** 点ごとの道のモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Dependent_Function.
Require Googology_In_Coq.Function.
Require Googology_In_Coq.Path.
Require Googology_In_Coq.Dependent_Pointwise_Path.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Dependent_Function (Dependent_Function).
Import Googology_In_Coq.Function (Function).
Import Googology_In_Coq.Path (Path).
Import Googology_In_Coq.Dependent_Pointwise_Path (Dependent_Pointwise_Path).

(** ライブラリを開きます。 *)

Definition
  Pointwise_Path@{i | } (A : Type@{i}) (B : Type@{i})
    : Function A B -> Function A B -> Type@{i}
    :=
      fun (f : Function A B) (g : Function A B) =>
        Dependent_Function
          A
          (fun x : A => Path (Function.apply f x) (Function.apply g x))
.
(* from: originally defined by Hexirp *)

(** 点ごとの道です。 *)

Definition
  apply@{i | }
      {A : Type@{i}}
      {B : Type@{i}}
      {f : Function A B}
      {g : Function A B}
    : Pointwise_Path A B f g -> forall x : A, Path (f x) (g x)
    :=
      fun (p : Pointwise_Path A B f g) (x : A) =>
        Dependent_Function.apply
          A
          (fun x : A => Path (Function.apply f x) (Function.apply g x))
          p
          x
.
(* from: originally defined by Hexirp *)

(** 点ごとの道を一点で具体化します。 *)

Definition
  id@{i | } {A : Type@{i}} {B : Type@{i}} {f : Function A B}
    : Pointwise_Path A B f f
    :=
      Dependent_Function.abstract
        A
        (fun x : A => Path (Function.apply f x) (Function.apply f x))
        (fun x : A => Path.id)
.
(* from: originally defined by Hexirp *)

(** 点ごとの恒等道です。 *)

Definition
  conc@{i | }
      {A : Type@{i}}
      {B : Type@{i}}
      {f : Function A B}
      {g : Function A B}
      {h : Function A B}
    :
        Pointwise_Path A B f g
      ->
        Pointwise_Path A B g h
      ->
        Pointwise_Path A B f h
    :=
      fun (p : Pointwise_Path A B f g) (q : Pointwise_Path A B g h) =>
        Dependent_Function.abstract
          A
          (fun x : A => Path (Function.apply f x) (Function.apply h x))
          (fun x : A => Path.conc (apply p x) (apply q x))
.
(* from: originally defined by Hexirp *)

(** 点ごとの道の合成です。 *)

Definition
  inv@{i | }
      {A : Type@{i}}
      {B : Type@{i}}
      {f : Function A B}
      {g : Function A B}
    : Pointwise_Path A B f g -> Pointwise_Path A B g f
    :=
      fun p : Pointwise_Path A B f g =>
        Dependent_Function.abstract
          A
          (fun x : A => Path (Function.apply g x) (Function.apply f x))
          (fun x : A => Path.inv (apply p x))
.
(* from: originally defined by Hexirp *)

(** 点ごとの道の逆です。 *)

Definition
  wisker_L@{i | }
      {A : Type@{i}}
      {B : Type@{i}}
      {C : Type@{i}}
      (f : Function B C)
      {g : Function A B}
      {h : Function A B}
    :
        Pointwise_Path A B g h
      ->
        Pointwise_Path A C (Function.comp f g) (Function.comp f h)
    :=
      fun p : Pointwise_Path A B g h =>
        Dependent_Function.abstract
          A
          (fun x : A => Path (f (g x)) (f (h x)))
          (fun x : A => Path.ap f (apply p x))
.
(* from: originally defined by Hexirp *)

(** 左からの髭つけです。 *)

Definition
  wisker_R@{i | }
      {A : Type@{i}}
      {B : Type@{i}}
      {C : Type@{i}}
      (f : Function A B)
      {g : Function B C}
      {h : Function B C}
    :
        Pointwise_Path B C g h
      ->
        Pointwise_Path A C (Function.comp g f) (Function.comp h f)
    :=
      fun p : Pointwise_Path B C g h =>
        Dependent_Function.abstract
          A
          (fun x : A => Path (g (f x)) (h (f x)))
          (fun x : A => apply p (Function.apply f x))
.
(* from: originally defined by Hexirp *)

(** 右からの髭つけです。 *)

Definition
  wisker_L_R@{i | }
      {A : Type@{i}}
      {B : Type@{i}}
      {C : Type@{i}}
      {D : Type@{i}}
      (f : Function C D)
      (h : Function A B)
      {g_L : Function B C}
      {g_R : Function B C}
    :
        Pointwise_Path B C g_L g_R
      ->
        Pointwise_Path
          A
          D
          (Function.comp f (Function.comp g_L h))
          (Function.comp f (Function.comp g_R h))
    := fun p : Pointwise_Path B C g_L g_R => wisker_L f (wisker_R h p)
.
(* from: originally defined by Hexirp *)

(** 左右からの髭つけです。 *)
