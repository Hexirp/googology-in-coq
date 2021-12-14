(** 依存直和型に関するモジュールです。 *)

Require Googology_In_Coq.Base.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.

(** ライブラリを開きます。 *)

Inductive
  Dependent_Sum@{i | } (A : Type@{i}) (B : A -> Type@{i}) : Type@{i}
    := pair : forall a : A, B a -> Dependent_Sum A B
.
(* from: originally defined by Hexirp *)

(** 依存直和型です。 *)

Arguments pair {A} {B} a b.

(** [pair] についての暗黙引数を設定します。 *)

Definition
  matching@{i | }
      {A : Type@{i}}
      {B : A -> Type@{i}}
      (P : Dependent_Sum A B -> Type@{i})
      (construct_pair : forall (a : A) (b : B a), P (pair a b))
    : forall x : Dependent_Sum A B, P x
    :=
      fun x : Dependent_Sum A B =>
        match x with pair a b => construct_pair a b end
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  matching_nodep@{i | }
      {A : Type@{i}}
      {B : A -> Type@{i}}
      {P : Type@{i}}
      (construct_pair : forall a : A, B a -> P)
    : Dependent_Sum A B -> P
    := matching (fun x_ : Dependent_Sum A B => P) construct_pair
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  first@{i | } {A : Type@{i}} {B : A -> Type@{i}} : Dependent_Sum A B -> A
    := matching_nodep (fun (a : A) (b : B a) => a)
.
(* from: originally defined by Hexirp *)

(** 依存直和型の第一射影関数です。 *)

Definition
  second@{i | } {A : Type@{i}} {B : A -> Type@{i}}
    : forall x : Dependent_Sum A B, B (first x)
    :=
      matching
        (fun x_ : Dependent_Sum A B => B (first x_))
        (fun (a : A) (b : B a) => b)
.
(* from: originally defined by Hexirp *)

(** 依存直和型の第二射影関数です。 *)
