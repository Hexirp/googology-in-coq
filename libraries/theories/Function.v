(** 関数型に関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Dependent_Function.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Dependent_Function (Dependent_Function).

(** ライブラリを開きます。 *)

Inductive
  Function@{i | } (A : Type@{i}) (B : Type@{i}) : Type@{i}
    := wrap : Dependent_Function@{i} A (fun x : A => B) -> Function A B
.
(* from: originally defined by Hexirp *)

(** 関数型です。 *)

Definition
  unwrap@{i | } (A : Type@{i}) (B : Type@{i})
    : Function@{i} A B -> A -> B
    := fun x : Function@{i} A B => match x with wrap _ _ x_v => x_v end
.
(* from: originally defined by Hexirp *)

(** 関数型です。 *)

Definition
  abstract@{i | } (A : Type@{i}) (B : Type@{i}) : (A -> B) -> Function@{i} A B
    := wrap A B
.
(* from: originally defined by Hexirp *)

(** 関数の抽象です。 *)

Definition
  apply@{i | } (A : Type@{i}) (B : Type@{i}) : Function@{i} A B -> A -> B
    := unwrap A B
.
(* from: originally defined by Hexirp *)

(** 関数の適用です。 *)

Definition
  id@{i | } (A : Type@{i}) : Function@{i} A A := abstract A A (fun x : A => x)
.
(* from: originally defined by Hexirp *)

(** 恒等関数です。 *)

Definition
  const@{i | } (A : Type@{i}) (B : Type@{i}) (x : A)
    : Function@{i} B A
    := abstract B A (fun y : B => x)
.
(* from: originally defined by Hexirp *)

(** 定数関数です。 *)

Definition
  comp@{i | } (A : Type@{i}) (B : Type@{i}) (C : Type@{i})
    : Function@{i} B C -> Function@{i} A B -> Function@{i} A C
    :=
      fun (f : Function@{i} B C) (g : Function@{i} A B) =>
        abstract A C (fun x : A => apply B C f (apply A B g x))
.
(* from: originally defined by Hexirp *)

(** 関数の合成です。 *)

Definition
  map@{i | }
      (A : Type@{i})
      (B : Type@{i})
      (C : Type@{i})
      (D : Type@{i})
      (f : C -> A)
      (g : B -> D)
    : Function@{i} A B -> Function@{i} C D
    :=
      fun x : Function@{i} A B =>
        abstract C D (fun y : C => g (apply A B x (f y)))
.
(* from: originally defined by Hexirp *)

(** 関数型の写像です。 *)
