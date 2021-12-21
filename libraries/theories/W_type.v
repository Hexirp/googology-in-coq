(** ウ型に関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Dependent_Function.
Require Googology_In_Coq.Function.
Require Googology_In_Coq.Dependent_Sum.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Dependent_Function (Dependent_Function).
Import Googology_In_Coq.Function (Function).
Import Googology_In_Coq.Dependent_Sum (Dependent_Sum).

(** ライブラリを開きます。 *)

Inductive
  W_type@{i | } (A : Type@{i}) (B : A -> Type@{i}) : Type@{i}
    :=
      sup
        :
            Dependent_Sum A (fun a : A => Function (B a) (W_type A B))
          ->
            W_type A B
.
(* from: originally defined by Hexirp *)

(** ウ型です。 W-types です。 *)

Arguments sup {A} {B} _.

(** [sup] の暗黙引数を設定します。 *)

Definition
  matching@{i | }
      {A : Type@{i}}
      {B : A -> Type@{i}}
      (P : W_type A B -> Type@{i})
      (
        constructor_sup
          :
            forall
              x_v : Dependent_Sum A (fun a : A => Function (B a) (W_type A B))
            ,
              P (sup x_v)
      )
    : forall x : W_type A B, P x
    :=
      fun x : W_type A B =>
        match x with sup x_v => constructor_sup x_v end
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  matching_nodep@{i | }
      {A : Type@{i}}
      {B : A -> Type@{i}}
      {P : Type@{i}}
      (
        constructor_sup
          :
            Dependent_Sum A (fun a : A => Function (B a) (W_type A B)) -> P
      )
    : W_type A B -> P
    :=
      fun x : W_type A B =>
        match x with sup x_v => constructor_sup x_v end
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  induction@{i | }
      {A : Type@{i}}
      {B : A -> Type@{i}}
      (P : W_type A B -> Type@{i})
      (
        constructor_sup
          :
            forall
              x_v : Dependent_Sum A (fun a : A => Function (B a) (W_type A B))
            ,
              Dependent_Function
                (B (Dependent_Sum.first x_v))
                (
                  fun x_v_2_x : B (Dependent_Sum.first x_v) =>
                    P (Function.apply (Dependent_Sum.second x_v) x_v_2_x)
                )
            ->
              P (sup x_v)
      )
    : forall x : W_type A B, P x
    :=
      fix induction (x : W_type A B) {struct x} : P x :=
        matching
          P
          (
            fun
              x_v : Dependent_Sum A (fun a : A => Function (B a) (W_type A B))
            =>
              constructor_sup
                x_v
                (
                  Dependent_Function.abstract
                    (B (Dependent_Sum.first x_v))
                    (
                      fun x_v_2_x : B (Dependent_Sum.first x_v) =>
                        P (Function.apply (Dependent_Sum.second x_v) x_v_2_x)
                    )
                    (
                      fun x_v_2_x : B (Dependent_Sum.first x_v) =>
                        induction
                          (Function.apply (Dependent_Sum.second x_v) x_v_2_x)
                    )
                )
          )
          x
.
(* from: originally defined by Hexirp *)

(** 帰納法の原理です。 *)

Definition
  recursion@{i | }
      {A : Type@{i}}
      {B : A -> Type@{i}}
      {P : Type@{i}}
      (
        constructor_sup
          :
            forall
              x_v : Dependent_Sum A (fun a : A => Function (B a) (W_type A B))
            ,
              Function (B (Dependent_Sum.first x_v)) P
            ->
              P
      )
    : W_type A B -> P
    := induction (fun x_ => P) constructor_sup
.
(* from: originally defined by Hexirp *)

(** 再帰です。 *)

Definition
  map@{i | }
      {A : Type@{i}}
      {B : A -> Type@{i}}
      {C : Type@{i}}
      {D : C -> Type@{i}}
      (f : A -> C)
      (g : forall x : A, D (f x) -> B x)
    : W_type A B -> W_type C D
    :=
      recursion
        (
          fun
            (x_v : Dependent_Sum A (fun a : A => Function (B a) (W_type A B)))
            (y : Function (B (Dependent_Sum.first x_v)) (W_type C D))
          =>
            sup
              (
                Dependent_Sum.pair
                  (f (Dependent_Sum.first x_v))
                  (
                    Function.abstract
                      (
                        fun z : D (f (Dependent_Sum.first x_v)) =>
                          Function.apply y (g (Dependent_Sum.first x_v) z)
                      )
                  )
              )
        )
.
(* from: originally defined by Hexirp *)

(** ウ型の写像です。 *)
