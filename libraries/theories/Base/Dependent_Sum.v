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

Definition first {A : Type} {B : A -> Type}
  : T A B -> A
  := fun x : T A B => match x with pair a b => a end
.
(* from: originally defined by Hexirp *)

(** 依存和型の第一射影関数です。 *)

Definition second {A : Type} {B : A -> Type}
  : forall x : T A B, B (first x)
  := fun x : T A B => match x with pair a b => b end
.
(* from: originally defined by Hexirp *)

(** 依存和型の第二射影関数です。 *)

Definition map {A : Type} {B : A -> Type} {C : A -> Type}
  : (forall x : A, B x -> C x) -> T A B -> T A C
  :=
    fun (f : forall x : A, B x -> C x) (x : T A B) =>
      match x with pair a b => pair a (f a b) end
.
(* from: originally defined by Hexirp *)

(** 依存和型の写像です。 *)
