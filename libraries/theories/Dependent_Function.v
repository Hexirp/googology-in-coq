(** 依存関数型のモジュールです。 *)

Require Googology_In_Coq.Base.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.

(** ライブラリを開きます。 *)

Inductive
  Dependent_Function@{i | } (A : Type@{i}) (B : A -> Type@{i}) : Type@{i}
    := wrap : (forall x : A, B x) -> Dependent_Function A B
.
(* from: originally defined by Hexirp *)

(** 依存関数型です。 *)

Definition
  unwrap@{i | } (A : Type@{i}) (B : A -> Type@{i})
    : Dependent_Function@{i} A B -> forall x : A, B x
    :=
      fun x : Dependent_Function@{i} A B =>
        match x with wrap _ _ x_v => x_v end
.
(* from: originally defined by Hexirp *)

(** 依存関数型です。 *)

Definition
  abstract@{i | } (A : Type@{i}) (B : A -> Type@{i})
    : (forall x : A, B x) -> Dependent_Function@{i} A B
    := wrap A B
.
(* from: originally defined by Hexirp *)

(** 抽象です。ラムダ抽象です。 *)

Definition
  matching@{i | }
      (A : Type@{i})
      (B : A -> Type@{i})
      (P : Dependent_Function@{i} A B -> Type@{i})
      (
        constructor_abstract
          : forall x_v : forall x : A, B x, P (abstract A B x_v)
      )
    : forall x : Dependent_Function@{i} A B, P x
    :=
      fun x : Dependent_Function@{i} A B =>
        match x as x_ return P x_ with
          wrap _ _ x_v => constructor_abstract A B x_v
        end
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  matching_nodep@{i | }
      (A : Type@{i})
      (B : A -> type@{i})
      (P : Type@{i})
      (constructor_abstract : (forall x : A, B x) -> P)
    : Dependent_Function@{i} A B -> P
    := matching_nodep A B (fun x_ : Dependent_Function@{i} A B => P)
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  apply@{i | } (A : Type@{i}) (B : A -> Type@{i})
    : Dependent_Function@{i} A B -> forall x : A, B x
    :=
      matching_nodep
        A
        B
        (forall x : A, B x)
        (fun x_v : forall x : A, B x => x_v)
.
(* from: originally defined by Hexirp *)

(** 適用です。 *)

(** [abstract] は構築子です。 [apply] は分解子です。甲を [abstract] で構築したものを [apply] で分解したものは甲と同じというのが β-変換です。甲を [apply] で分解したものを [abstract] で構築したものは甲と同じというのが η-変換です。「全てのイに対して甲をイに適用したものと乙をイに適用したものが同じである」であれば甲を [abstract] で構築したものと乙を [abstract] で構築したものが同じというのが判断同値の関数外延性です。甲と乙が同じかつイとロが同じであれば甲を [apply] で分解したものをイに適用したものと乙を [apply] で分解したものをロに適用したものは同じであるというのがホニャララです。 *)

Definition
  map@{i | }
      (A : Type@{i})
      (B : A -> Type@{i})
      (C : Type@{i})
      (D : C -> Type@{i})
      (f : C -> A)
      (g : forall x : C, B (f x) -> D x)
    : Dependent_Function A B -> Dependent_Function C D
    :=
      fun x : Dependent_Function A B =>
        abstract C D (fun y : C => g y (apply A B x (f y)))
.
(* from: originally defined by Hexirp *)

(** 依存関数型の写像です。 *)
