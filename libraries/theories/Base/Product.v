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

Definition first {A : Type} {B : Type} : T A B -> A
  := fun x : T A B => match x with pair a b => a end
.
(* from: originally defined by Hexirp *)

(** 直積型の第一射影関数です。 *)

Definition second {A : Type} {B : Type} : T A B -> B
  := fun x : T A B => match x with pair a b => b end
.
(* from: originally defined by Hexirp *)

(** 直積型の第二射影関数です。 *)

Definition map {A : Type} {B : Type} {C : Type} {D : Type}
  : (A -> C) -> (B -> D) -> T A B -> T C D
  :=
    fun (f_a : A -> C) (f_b : B -> D) (x : T A B) =>
      match x with pair a b => pair (f_a a) (f_b b) end
.
(* from: originally defined by Hexirp *)

(** 直積型への写像です。 *)

Definition curry {A : Type} {B : Type} {C : Type}
  : (T A B -> C) -> A -> B -> C
  := fun (f : T A B -> C) (x : A) (y : B) => f (pair x y)
.
(* from: originally defined by Hexirp *)

(** 関数のカリー化です。 *)

Definition uncurry {A : Type} {B : Type} {C : Type}
  : (A -> B -> C) -> T A B -> C
  :=
    fun (f : A -> B -> C) (x : T A B) =>
      match x with pair a b => f a b end
.
(* from: originally defined by Hexirp *)

(** 関数の非カリー化です。 *)
