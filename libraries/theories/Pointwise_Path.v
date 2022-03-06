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

Inductive
  Pointwise_Path@{i | }
      (A : Type@{i})
      (B : Type@{i})
      (f : Function@{i} A B)
      (g : Function@{i} A B)
    : Type@{i}
    :=
      wrap
        :
            Dependent_Function@{i}
              A
              (
                fun x : A =>
                  Path@{i} B (Function.apply A B f x) (Function.apply A B g x)
              )
          ->
            Pointwise_Path A B f g
.
(* from: originally defined by Hexirp *)

(** 点ごとの道です。 *)

Definition
  unwrap@{i | }
      (A : Type@{i})
      (B : Type@{i})
      (f : Function@{i} A B)
      (g : Function@{i} A B)
    :
        Pointwise_Path@{i} A B f g
      ->
        Dependent_Function@{i}
          A
          (
            fun x : A =>
              Path@{i} B (Function.apply A B f x) (Function.apply A B g x)
          )
    :=
      fun x : Pointwise_Path A B f g =>
        match x with wrap _ _ _ _ x_v => x_v end
.
(* from: originally defined by Hexirp *)

(** 点ごとの道です。 *)

Definition
  abstract@{i | }
      (A : Type@{i})
      (B : Type@{i})
      (f : Function@{i} A B)
      (g : Function@{i} A B)
    :
        (
          forall x : A,
            Path@{i} B (Function.apply A B f x) (Function.apply A B g x)
        )
      ->
        Pointwise_Path@{i} A B f g
    :=
      fun
        x
          :
            forall x : A,
              Path@{i} B (Function.apply A B f x) (Function.apply A B g x)
      =>
        wrap A B f g
          (
            Dependent_Function.abstract
              A
              (
                fun x : A =>
                  Path@{i} B (Function.apply A B f x) (Function.apply A B g x)
              )
              x
          )
.
(* from: originally defined by Hexirp *)

(** 点ごとの道を作成します。 *)

Definition
  apply@{i | }
      (A : Type@{i})
      (B : Type@{i})
      (f : Function@{i} A B)
      (g : Function@{i} A B)
    :
        Pointwise_Path@{i} A B f g
      ->
        forall x : A,
          Path@{i} B (Function.apply A B f x) (Function.apply A B g x)
    :=
      fun x : Pointwise_Path@{i} A B f g =>
        Dependent_Function.apply
          A
          (
            fun x : A =>
              Path@{i} B (Function.apply A B f x) (Function.apply A B g x)
          )
          (unwrap A B f g x)
.
(* from: originally defined by Hexirp *)

(** 点ごとの道を一点で具体化します。 *)

Definition
  id@{i | } (A : Type@{i}) (B : Type@{i}) (f : Function@{i} A B)
    : Pointwise_Path@{i} A B f f
    :=
      abstract
        A
        B
        f
        f
        (fun x : A => Path.id B (Function.apply A B f x))
.
(* from: originally defined by Hexirp *)

(** 点ごとの恒等道です。 *)

Definition
  conc@{i | }
      (A : Type@{i})
      (B : Type@{i})
      (f : Function@{i} A B)
      (g : Function@{i} A B)
      (h : Function@{i} A B)
    :
        Pointwise_Path@{i} A B f g
      ->
        Pointwise_Path@{i} A B g h
      ->
        Pointwise_Path@{i} A B f h
    :=
      fun
        (p : Pointwise_Path@{i} A B f g)
        (q : Pointwise_Path@{i} A B g h)
      =>
        abstract
          A
          B
          f
          h
          (
            fun x : A =>
              Path.conc
                B
                (Function.apply A B f x)
                (Function.apply A B g x)
                (Function.apply A B h x)
                (apply A B f g p x)
                (apply A B g h q x)
          )
.
(* from: originally defined by Hexirp *)

(** 点ごとの道の合成です。 *)

Definition
  inv@{i | }
      (A : Type@{i})
      (B : Type@{i})
      (f : Function@{i} A B)
      (g : Function@{i} A B)
    : Pointwise_Path@{i} A B f g -> Pointwise_Path@{i} A B g f
    :=
      fun p : Pointwise_Path@{i} A B f g =>
        abstract
          A
          B
          g
          f
          (
            fun x : A =>
              Path.inv
                B
                (Function.apply A B f x)
                (Function.apply A B g x)
                (apply A B f g p x)
          )
.
(* from: originally defined by Hexirp *)

(** 点ごとの道の逆です。 *)

Definition
  wisker_L@{i | }
      (A : Type@{i})
      (B : Type@{i})
      (C : Type@{i})
      (f : Function@{i} B C)
      (g_L : Function@{i} A B)
      (g_R : Function@{i} A B)
    :
        Pointwise_Path@{i} A B g_L g_R
      ->
        Pointwise_Path@{i}
          A
          C
          (Function.comp A B C f g_L)
          (Function.comp A B C f g_R)
    :=
      fun p : Pointwise_Path@{i} A B g_L g_R =>
        abstract
          A
          C
          (Function.comp A B C f g_L)
          (Function.comp A B C f g_R)
          (
            fun x : A =>
              Path.ap
                B
                C
                (Function.apply B C f)
                (Function.apply A B g_L x)
                (Function.apply A B g_R x)
                (apply A B g_L g_R p x)
          )
.
(* from: originally defined by Hexirp *)

(** 左からの髭つけです。 *)

Definition
  wisker_R@{i | }
      (A : Type@{i})
      (B : Type@{i})
      (C : Type@{i})
      (f_L : Function@{i} B C)
      (f_R : Function@{i} B C)
      (g : Function@{i} A B)
    :
        Pointwise_Path@{i} B C f_L f_R
      ->
        Pointwise_Path@{i}
          A
          C
          (Function.comp A B C f_L g)
          (Function.comp A B C f_R g)
    :=
      fun p : Pointwise_Path@{i} B C f_L f_R =>
        abstract
          A
          C
          (Function.comp A B C f_L g)
          (Function.comp A B C f_R g)
          (
            fun x : A =>
              apply
                B
                C
                f_L
                f_R
                p
                (Function.apply A B g x)
          )
.
(* from: originally defined by Hexirp *)

(** 右からの髭つけです。 *)

Definition
  wisker_L_R@{i | }
      (A : Type@{i})
      (B : Type@{i})
      (C : Type@{i})
      (D : Type@{i})
      (f : Function@{i} C D)
      (g_L : Function@{i} B C)
      (g_R : Function@{i} B C)
      (h : Function@{i} A B)
    :
        Pointwise_Path@{i} B C g_L g_R
      ->
        Pointwise_Path@{i}
          A
          D
          (Function.comp A C D f (Function.comp A B C g_L h))
          (Function.comp A C D f (Function.comp A B C g_R h))
    :=
      fun p : Pointwise_Path@{i} B C g_L g_R =>
        wisker_L
          A
          C
          D
          f
          (Function.comp A B C g_L h)
          (Function.comp A B C g_R h)
          (
            wisker_R
              A
              B
              C
              g_L
              g_R
              h
              p
          )
.
(* from: originally defined by Hexirp *)

(** 左右からの髭つけです。 *)
