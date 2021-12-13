(** 直積の型に関するモジュールです。 *)

Require Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を要求します。 *)

Import Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を開きます。 *)

Inductive T (A : Type) (B : Type)
  : Type
  := pair : A -> B -> T A B
.
(* from: originally defined by Hexirp *)

(** 主型です。 *)

Arguments pair {A} {B} a b.

(** [pair] についての暗黙引数を設定します。 *)

Definition induction
    {A : Type}
    {B : Type}
    (P : T A B -> Type)
    (construct_pair : forall (x_1 : A) (x_2 : B), P (pair x_1 x_2))
  : forall x : T A B, P x
  := fun x : T A B => match x with pair a b => construct_pair a b end
.
(* from: originally defined by Hexirp *)

(** 帰納法です。 *)

Definition recursion
    {A : Type}
    {B : Type}
    {P : Type}
    (construct_pair : A -> B -> P)
  : T A B -> P
  := induction (fun x_ : T A B => P) construct_pair
.
(* from: originally defined by Hexirp *)

(** 再帰です。 *)

Definition first {A : Type} {B : Type} : T A B -> A
  := recursion (fun (a : A) (b : B) => a)
.
(* from: originally defined by Hexirp *)

(** 直積型の第一射影関数です。 *)

Definition second {A : Type} {B : Type} : T A B -> B
  := recursion (fun (a : A) (b : B) => b)
.
(* from: originally defined by Hexirp *)

(** 直積型の第二射影関数です。 *)

Definition map {A : Type} {B : Type} {C : Type} {D : Type}
  : (A -> C) -> (B -> D) -> T A B -> T C D
  :=
    fun (f_a : A -> C) (f_b : B -> D) =>
      recursion (fun (a : A) (b : B) => pair (f_a a) (f_b b))
.
(* from: originally defined by Hexirp *)

(** 直積型での写像です。 *)

Definition curry {A : Type} {B : Type} {C : Type}
  : (T A B -> C) -> A -> B -> C
  := fun (f : T A B -> C) (x : A) (y : B) => f (pair x y)
.
(* from: originally defined by Hexirp *)

(** 関数のカリー化です。 *)

Definition uncurry {A : Type} {B : Type} {C : Type}
  : (A -> B -> C) -> T A B -> C
  :=
    fun f : A -> B -> C =>
      recursion (fun (a : A) (b : B) => f a b)
.
(* from: originally defined by Hexirp *)

(** 関数の非カリー化です。 *)
