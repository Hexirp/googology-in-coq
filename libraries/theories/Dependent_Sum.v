(** 依存和の型に関するモジュールです。 *)

Require Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を要求します。 *)

Import Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を開きます。 *)

Inductive T (A : Type) (B : A -> Type)
  : Type
  := pair : forall a : A, B a -> T A B
.
(* from: originally defined by Hexirp *)

(** 主型です。 *)

Arguments pair {A} {B} a b.

(** [pair] についての暗黙引数を設定します。 *)

Definition induction
    {A : Type}
    {B : A -> Type}
    (P : T A B -> Type)
    (construct_pair : forall (a : A) (b : B a), P (pair a b))
  : forall x : T A B, P x
  := fun x : T A B => match x with pair a b => construct_pair a b end
.
(* from: originally defined by Hexirp *)

(** 帰納法です。 *)

Definition recursion
    {A : Type}
    {B : A -> Type}
    {P : Type}
    (construct_pair : forall a : A, B a -> P)
  : T A B -> P
  := induction (fun x_ : T A B => P) construct_pair
.
(* from: originally defined by Hexirp *)

(** 再帰です。 *)

Definition first {A : Type} {B : A -> Type}
  : T A B -> A
  := recursion (fun (a : A) (b : B a) => a)
.
(* from: originally defined by Hexirp *)

(** 依存和型の第一射影関数です。 *)

Definition second {A : Type} {B : A -> Type}
  : forall x : T A B, B (first x)
  := induction (fun x_ : T A B => B (first x_)) (fun (a : A) (b : B a) => b)
.
(* from: originally defined by Hexirp *)

(** 依存和型の第二射影関数です。 *)

Definition map {A : Type} {B : A -> Type} {C : A -> Type}
  : (forall x : A, B x -> C x) -> T A B -> T A C
  :=
    fun f : forall x : A, B x -> C x =>
      recursion (fun (a : A) (b : B a) => pair a (f a b))
.
(* from: originally defined by Hexirp *)

(** 依存和型の写像です。 *)
