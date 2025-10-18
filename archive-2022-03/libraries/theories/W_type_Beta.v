(** ウ型のベータに関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Function.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Function (Function).

(** ライブラリを開きます。 *)

Inductive
  W_type_Beta@{i | }
      (t : forall A : Type@{i}, (A -> Type@{i}) -> Type@{i})
      (A : Type@{i})
      (B : A -> Type@{i})
      (a : A)
    : Type@{i}
    := wrap : Function@{i} (B a) (t A B) -> W_type_Beta t A B a
.
(* from: originally defined by Hexirp *)

(** ウ型のベータです。 *)

Definition
  unwrap@{i | }
      (t : forall A : Type@{i}, (A -> Type@{i}) -> Type@{i})
      (A : Type@{i})
      (B : A -> Type@{i})
      (a : A)
    : W_type_Beta@{i} t A B a -> Function@{i} (B a) (t A B)
    :=
      fun x : W_type_Beta@{i} t A B a =>
        match x with wrap _ _ _ _ x_v => x_v end
.
(* from: originally defined by Hexirp *)

(** ウ型のベータです。 *)

Definition
  abstract@{i | }
      (t : forall A : Type@{i}, (A -> Type@{i}) -> Type@{i})
      (A : Type@{i})
      (B : A -> Type@{i})
      (a : A)
    : (B a -> t A B) -> W_type_Beta@{i} t A B a
    :=
      fun x : B a -> t A B =>
        wrap t A B a (Function.abstract (B a) (t A B) x)
.
(* from: originally defined by Hexirp *)

(** ウ型のベータの抽象です。 *)

Definition
  apply@{i | }
      (t : forall A : Type@{i}, (A -> Type@{i}) -> Type@{i})
      (A : Type@{i})
      (B : A -> Type@{i})
      (a : A)
    : W_type_Beta@{i} t A B a -> B a -> t A B
    :=
      fun x : W_type_Beta@{i} t A B a =>
        Function.apply (B a) (t A B) (unwrap t A B a x)
.
(* from: originally defined by Hexirp *)

(** ウ型のベータの適用です。 *)
