(** 関数の型に関するモジュールです。 *)

Require Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を要求します。 *)

Import Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を開きます。 *)

Definition id {A : Type}
  : A -> A
  := fun x : A => x
.
(* from: originally defined by Hexirp *)

(** 恒等関数です。 *)

Definition const {A : Type} {B : Type}
  : A -> B -> A
  := fun x : A => fun y : B => x
.
(* from: originally defined by Hexirp *)

(** 定数関数です。 *)

Definition comp {A : Type} {B : Type} {C : Type}
  : (B -> C) -> (A -> B) -> A -> C
  := fun (f : B -> C) (g : A -> B) (x : A) => f (g x)
.
(* from: originally defined by Hexirp *)

(** 関数の合成です。 *)

Definition apply {A : Type} {B : Type}
  : (A -> B) -> A -> B
  := fun (f : A -> B) (x : A) => f x
.
(* from: originally defined by Hexirp *)

(** 関数の適用です。 *)

Definition domain {A : Type} {B : Type}
  : (A -> B) -> Type
  := fun f : A -> B => A
.
(* from: originally defined by Hexirp *)

(** 関数の定義域です。あるいは始域です。 *)

Definition codomain {A : Type} {B : Type}
  : (A -> B) -> Type
  := fun f : A -> B => B
.
(* from: originally defined by Hexirp *)

(** 関数の値域です。あるいは終域です。 *)
