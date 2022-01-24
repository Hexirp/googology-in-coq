(** 点ごとの道の点ごとの道のモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Dependent_Function.
Require Googology_In_Coq.Function.
Require Googology_In_Coq.Path.
Require Googology_In_Coq.Pointwise_Path.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Dependent_Function (Dependent_Function).
Import Googology_In_Coq.Function (Function).
Import Googology_In_Coq.Path (Path).
Import Googology_In_Coq.Pointwise_Path (Pointwise_Path).

(** ライブラリを開きます。 *)

Definition
  Pointwise_Path_Pointwise_Path@{i | }
      {A : Type@{i}}
      {B : Type@{i}}
      (f : Function A B)
      (g : Function A B)
    : Pointwise_Path A B f g -> Pointwise_Path A B f g -> Type@{i}
    :=
      fun (p : Pointwise_Path A B f g) (q : Pointwise_Path A B f g) =>
        Dependent_Function
          A
          (
            fun x : A =>
              Path (Path B (f x) (g x)) (Pointwise_Path.apply p x) (Pointwise_Path.apply q x)
          )
.
(* from: originally defined by Hexirp *)

(** 点ごとの道の点ごとの道です。 *)
