(** 点ごとの道のモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Dependent_Function.
Require Googology_In_Coq.Path.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Dependent_Function (Dependent_Function).
Import Googology_In_Coq.Path (Path).

(** ライブラリを開きます。 *)

Inductive
  Dependent_Pointwise_Path@{i | }
      (A : Type@{i})
      (B : A -> Type@{i})
      (f : Dependent_Function@{i} A B)
      (g : Dependent_Function@{i} A B)
    : Type@{i}
    :=
      wrap
        :
            Dependent_Function@{i}
              A
              (
                fun x : A =>
                  Path@{i}
                    (B x)
                    (Dependent_Function.apply A B f x)
                    (Dependent_Function.apply A B g x)
              )
          ->
            Dependent_Pointwise_Path A B f g
.
(* from: originally defined by Hexirp *)

(** 点ごとの道です。 *)

Definition
  unwrap@{i | }
      (A : Type@{i})
      (B : A -> Type@{i})
      (f : Dependent_Function@{i} A B)
      (g : Dependent_Function@{i} A B)
    :
        Dependent_Pointwise_Path@{i} A B f g
      ->
        Dependent_Function@{i}
          A
          (
            fun x : A =>
              Path@{i}
                (B x)
                (Dependent_Function.apply A B f x)
                (Dependent_Function.apply A B g x)
          )
    :=
      fun x : Dependent_Pointwise_Path@{i} A B f g =>
        match x with wrap _ _ _ _ x_v => x_v end
.
(* from: originally defined by Hexirp *)

(** 点ごとの道です。 *)

Definition
  abstract@{i | }
      (A : Type@{i})
      (B : A -> Type@{i})
      (f : Dependent_Function@{i} A B)
      (g : Dependent_Function@{i} A B)
    :
        (
          forall x : A,
            Path@{i}
              (B x)
              (Dependent_Function.apply A B f x)
              (Dependent_Function.apply A B g x)
        )
      ->
        Dependent_Pointwise_Path@{i} A B f g
    :=
      fun
        x : forall x : A,
          Path@{i}
            (B x)
            (Dependent_Function.apply A B f x)
            (Dependent_Function.apply A B g x)
      =>
        wrap A B f g
          (
            Dependent_Function.abstract
              A
              (
                fun x : A =>
                  Path@{i}
                    (B x)
                    (Dependent_Function.apply A B f x)
                    (Dependent_Function.apply A B g x)
              )
              x
          )
.
(* from: originally defined by Hexirp *)

(** 点ごとの道を作成します。 *)

Definition
  apply@{i | }
      (A : Type@{i})
      (B : A -> Type@{i})
      (f : Dependent_Function@{i} A B)
      (g : Dependent_Function@{i} A B)
    :
        Dependent_Pointwise_Path@{i} A B f g
      ->
        forall x : A,
          Path@{i}
            (B x)
            (Dependent_Function.apply A B f x)
            (Dependent_Function.apply A B g x)
    :=
      fun x : Dependent_Pointwise_Path A B f g =>
        Dependent_Function.apply
          A
          (
            fun x : A =>
              Path@{i}
                (B x)
                (Dependent_Function.apply A B f x)
                (Dependent_Function.apply A B g x)
          )
          (unwrap A B f g x)
.
(* from: originally defined by Hexirp *)

(** 点ごとの道を一点で具体化します。 *)

Definition
  id@{i | } (A : Type@{i}) (B : A -> Type@{i}) (f : Dependent_Function@{i} A B)
    : Dependent_Pointwise_Path@{i} A B f f
    :=
      abstract
        A
        B
        f
        f
        (fun x : A => Path.id (B x) (Dependent_Function.apply A B f x))
.
(* from: originally defined by Hexirp *)

(** 点ごとの恒等道です。 *)

Definition
  conc@{i | }
      (A : Type@{i})
      (B : A -> Type@{i})
      (f : Dependent_Function@{i} A B)
      (g : Dependent_Function@{i} A B)
      (h : Dependent_Function@{i} A B)
    :
        Dependent_Pointwise_Path@{i} A B f g
      ->
        Dependent_Pointwise_Path@{i} A B g h
      ->
        Dependent_Pointwise_Path@{i} A B f h
    :=
      fun
        (p : Dependent_Pointwise_Path@{i} A B f g)
        (q : Dependent_Pointwise_Path@{i} A B g h)
      =>
        abstract
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
      (f : Dependent_Function@{i} A B)
      (g : Dependent_Function@{i} A B)
    :
        Dependent_Pointwise_Path@{i} A B f g
      ->
        Dependent_Pointwise_Path@{i} A B g f
    :=
      fun p : Dependent_Pointwise_Path A B f g =>
        abstract
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
