(** 点ごとの道のモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Dependent_Function.
Require Googology_In_Coq.Path.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Dependent_Function (Dependent_Function).
Import Googology_In_Coq.Path (Path).

(** ライブラリを開きます。 *)

Definition
  Dependent_Pointwise_Path@{i | } (A : Type@{i}) (B : A -> Type@{i})
    : Dependent_Function A B -> Dependent_Function A B -> Type@{i}
    :=
      fun (f : Dependent_Function A B) (g : Dependent_Function A B) =>
        Dependent_Function
          A
          (
            fun x : A =>
              Path
                (B x)
                (Dependent_Function.apply A B f x)
                (Dependent_Function.apply A B g x)
          )
.
(* from: originally defined by Hexirp *)

(** 点ごとの道です。 *)

Definition
  abstract@{i | }
      (A : Type@{i})
      (B : A -> Type@{i})
      (f : Dependent_Function A B)
      (g : Dependent_Function A B)
    :
        (
          forall x : A,
            Path
              (B x)
              (Dependent_Function.apply A B f x)
              (Dependent_Function.apply A B g x)
        )
      ->
        Dependent_Pointwise_Path A B f g
    :=
      Dependent_Function.abstract
        A
        (
          fun x : A =>
            Path
              (B x)
              (Dependent_Function.apply A B f x)
              (Dependent_Function.apply A B g x)
        )
.

Definition
  apply@{i | }
      (A : Type@{i})
      (B : A -> Type@{i})
      (f : Dependent_Function A B)
      (g : Dependent_Function A B)
    :
        Dependent_Pointwise_Path A B f g
      ->
        forall x : A,
          Path
            (B x)
            (Dependent_Function.apply A B f x)
            (Dependent_Function.apply A B g x)
    :=
      fun (p : Dependent_Pointwise_Path A B f g) (x : A) =>
        Dependent_Function.apply
          A
          (
            fun x : A =>
              Path
                (B x)
                (Dependent_Function.apply A B f x)
                (Dependent_Function.apply A B g x)
          )
          p
          x
.
(* from: originally defined by Hexirp *)

(** 点ごとの道を一点で具体化します。 *)

Definition
  id@{i | } (A : Type@{i}) (B : A -> Type@{i}) (f : Dependent_Function A B)
    : Dependent_Pointwise_Path A B f f
    :=
      abstract
        A
        B
        f
        f
        (fun x : A => (Path.id (B x) (Dependent_Function.apply A B f x)))
.
(* from: originally defined by Hexirp *)

(** 点ごとの恒等道です。 *)

Definition
  conc@{i | }
      (A : Type@{i})
      (B : A -> Type@{i})
      (f : Dependent_Function A B)
      (g : Dependent_Function A B)
      (h : Dependent_Function A B)
    :
        Dependent_Pointwise_Path A B f g
      ->
        Dependent_Pointwise_Path A B g h
      ->
        Dependent_Pointwise_Path A B f h
    :=
      fun
        (p : Dependent_Pointwise_Path A B f g)
        (q : Dependent_Pointwise_Path A B g h)
      =>
        Dependent_Function.abstract
          A
          B
          f
          h
          (
            fun x : A =>
              Path.conc
                (B x)
                (Dependent_Function.apply A B f x)
                (Dependent_Function.apply A B g x)
                (Dependent_Function.apply A B h x)
                (apply A B f g p x)
                (apply A B g h q x)
          )
.
(* from: originally defined by Hexirp *)

(** 点ごとの道の合成です。 *)

Definition
  inv@{i | }
      (A : Type@{i})
      (B : A -> Type@{i})
      (f : Dependent_Function A B)
      (g : Dependent_Function A B)
    : Dependent_Pointwise_Path A B f g -> Dependent_Pointwise_Path A B g f
    :=
      fun p : Dependent_Pointwise_Path A B f g =>
        Dependent_Function.abstract
          A
          B
          g
          f
          (
            fun x : A =>
              Path.inv
                (B x)
                (Dependent_Function.apply A B f x)
                (Dependent_Function.apply A B g x)
                (apply A B f g p x)
          )
.
(* from: originally defined by Hexirp *)

(** 点ごとの道の逆です。 *)
