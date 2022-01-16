(** 関数型に関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Dependent_Function.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Dependent_Function (Dependent_Function).

(** ライブラリを開きます。 *)

Definition Function@{i | } (A : Type@{i}) (B : Type@{i}) : Type@{i} := A -> B.
(* from: originally defined by Hexirp *)

(** 関数型です。 *)

Definition id@{i | } (A : Type@{i}) : A -> A := fun x : A => x.
(* from: originally defined by Hexirp *)

(** 恒等関数です。 *)

Definition
  const@{i | } (A : Type@{i}) (B : Type@{i}) : A -> B -> A
    := fun (x : A) (y : B) => x
.
(* from: originally defined by Hexirp *)

(** 定数関数です。 *)

Definition
  comp@{i | } (A : Type@{i}) (B : Type@{i}) (C : Type@{i})
    : (B -> C) -> (A -> B) -> A -> C
    := fun (f : B -> C) (g : A -> B) (x : A) => f (g x)
.
(* from: originally defined by Hexirp *)

(** 関数の合成です。 *)

Definition
  apply@{i | } (A : Type@{i}) (B : Type@{i}) : (A -> B) -> A -> B
    := fun (f : A -> B) (x : A) => f x
.
(* from: originally defined by Hexirp *)

(** 関数の適用です。 *)

Definition
  abstract@{i | } (A : Type@{i}) (B : Type@{i}) : (A -> B) -> A -> B
    := fun (f : A -> B) (x : A) => f x
.
(* from: originally defined by Hexirp *)

(** 関数の抽象です。 *)

Definition
  domain@{i j | } (A : Type@{i}) (B : Type@{j}) : (A -> B) -> Type@{i}
    := fun f : A -> B => A
.
(* from: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/ *)

(** 関数の定義域です。あるいは始域です。 *)

Definition
  codomain@{i j | } (A : Type@{i}) (B : Type@{j}) : (A -> B) -> Type@{j}
    := fun f : A -> B => B
.
(* from: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/ *)

(** 関数の値域です。あるいは終域です。 *)

Definition
  map@{i | }
      (A : Type@{i})
      (B : Type@{i})
      (C : Type@{i})
      (D : Type@{i})
      (f : C -> A)
      (g : B -> D)
    : Function@{i} A B -> Function@{i} C D
    := fun (x : Function@{i} A B) (y : C) => g (x (f y))
.
(* from: originally defined by Hexirp *)

(** 関数型の写像です。 *)
