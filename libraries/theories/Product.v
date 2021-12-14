(** 直積型に関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Dependent_Sum.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Dependent_Sum (Dependent_Sum).

(** ライブラリを開きます。 *)

Definition
  Product@{i | } (A : Type@{i}) (B : Type@{i}) : Type@{i}
    := Dependent_Sum A (fun a : A => B)
.
(* from: originally defined by Hexirp *)

(** 直積型です。 *)

Definition
  pair@{i | } {A : Type@{i}} {B : Type@{i}} : A -> B -> Product A B
    := fun (x_1 : A) (x_2 : B) => Dependent_Sum.pair x_1 x_2
.

(** ペアリング関数です。 *)

Definition
  matching@{i | }
      {A : Type@{i}}
      {B : Type@{i}}
      (P : Product A B -> Type@{i})
      (construct_pair : forall (x_1 : A) (x_2 : B), P (pair x_1 x_2))
    : forall x : Product A B, P x
    := Dependent_Sum.matching P construct_pair
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  matching_nodep@{i | }
      {A : Type@{i}}
      {B : Type@{i}}
      {P : Type@{i}}
      (construct_pair : A -> B -> P)
    : Product A B -> P
    := matching (fun x_ : Product A B => P) construct_pair
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  first@{i | } {A : Type@{i}} {B : Type@{i}} : Product A B -> A
    := matching_nodep (fun (a : A) (b : B) => a)
.
(* from: originally defined by Hexirp *)

(** 直積型の第一射影関数です。 *)

Definition
  second@{i | } {A : Type@{i}} {B : Type@{i}} : Product A B -> B
    := matching_nodep (fun (a : A) (b : B) => b)
.
(* from: originally defined by Hexirp *)

(** 直積型の第二射影関数です。 *)

Definition
  curry@{i | } {A : Type@{i}} {B : Type@{i}} {C : Type@{i}}
    : (Product A B -> C) -> A -> B -> C
    := fun (f : Product A B -> C) (x : A) (y : B) => f (pair x y)
.
(* from: originally defined by Hexirp *)

(** 関数のカリー化です。 *)

Definition
  uncurry@{i | } {A : Type@{i}} {B : Type@{i}} {C : Type@{i}}
    : (A -> B -> C) -> Product A B -> C
    :=
      fun f : A -> B -> C =>
        matching_nodep (fun (a : A) (b : B) => f a b)
.
(* from: originally defined by Hexirp *)

(** 関数の非カリー化です。 *)
