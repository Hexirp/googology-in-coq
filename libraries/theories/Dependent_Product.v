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
