(** 依存直積型についてのモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Dependent_Function.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Dependent_Function (Dependent_Function).

(** ライブラリを開きます。 *)

Inductive
  Dependent_Product@{i | } (A : Type@{i}) (B : A -> Type@{i}) : Type@{i}
    := wrap : Dependent_Function@{i} A B -> Dependent_Product A B
.
(* from: originally defined by Hexirp *)

(** 依存直積型です。 *)

Definition
  unwrap@{i | } (A : Type@{i}) (B : A -> Type@{i})
    : Dependent_Product@{i} A B -> Dependent_Function@{i} A B
    :=
      fun x : Dependent_Product@{i} A B =>
        match x with wrap _ _ x_v => x_v end
.
(* from: originally defined by Hexirp *)

(** 関数型です。 *)

Definition
  abstract@{i | } (A : Type@{i}) (B : A -> Type@{i})
    : (forall x : A, B x) -> Dependent_Product@{i} A B
    :=
      fun x : forall x : A, B x =>
        wrap A B (Dependent_Function.wrap A B x)
.
(* from: originally defined by Hexirp *)

(** 関数の抽象です。 *)

Definition
  apply@{i | } (A : Type@{i}) (B : A -> Type@{i})
    : Dependent_Product@{i} A B -> forall x : A, B x
    :=
      fun x : Dependent_Product@{i} A B =>
        Dependent_Function.unwrap A B (unwrap A B x)
.
(* from: originally defined by Hexirp *)

(** 関数の適用です。 *)

Definition
  map@{i | }
      (A : Type@{i})
      (B : A -> Type@{i})
      (C : Type@{i})
      (D : C -> Type@{i})
      (f : C -> A)
      (g : forall x : C, B (f x) -> D x)
    : Dependent_Product@{i} A B -> Dependent_Product@{i} C D
    :=
      fun x : Dependent_Product@{i} A B =>
        abstract C D (fun y : C => g y (apply A B x (f y)))
.
(* from: originally defined by Hexirp *)

(** 依存直積型の写像です。 *)
