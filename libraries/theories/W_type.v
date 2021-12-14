(** ウ型に関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Function.
Require Googology_In_Coq.Dependent_Sum.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
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

Argument sup {A} {B} _.

(** [sup] の暗黙引数を設定します。 *)

Definition
  matching@{i | }
      {A : Type@{i}}
      {B : A -> Type@{i}}
      (P : W_type A B -> Type@{i})
      (
        construct_sup
          :
            forall
              x_v : Dependent_Sum A (fun a : A => Function (B a) (W_type A B))
            ,
              P (sup x_v)
    )
    : forall x : W_type A B, P x
    :=
      fun x : W_type A B =>
        match x with sup x_v => construct_sup x_v end
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  matching_nodep@{i | }
      {A : Type@{i}}
      {B : A -> Type@{i}}
      {P : Type@{i}}
      (
        construct_sup
          :
            Dependent_Sum A (fun a : A => Function (B a) (W_type A B)) -> P
    )
    : W_type A B -> P 
    :=
      fun x : W_type A B =>
        match x with sup x_v => construct_sup x_v end
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  induction@{i s_i | i < s_i}
      {A : Type@{i}}
      {B : A -> Type@{i}}
      (P : W_type A B -> Type@{i})
      (
        construct_sup
          :
            forall
              x_v : Dependent_Sum A (fun a : A => Function (B a) (W_type A B))
            ,
                Dependent_Sum.matching_nodep@{s_i}
                  (
                    fun
                      (x_v_1 : A)
                      (fun x_v_2 : Function (B x_v_1) (W_type A B))
                    =>
                      Dependent_Function.abstract
                        (
                          forall x_v_2_x : B x_v_1,
                            P (Function.apply x_v_2 x_v_2_x)
                        )
                  )
                  x_v
              ->
                P (sup x_v)
      )
    : forall x : W_type A B, P x
    :=
      fix induction (x : W_type A B) {struct x} : P x =>
        matching
          P
          (
            fun
              x_v : Dependent_Sum A (fun a : A => Function (B a) (W_type A B))
            =>
              construct_sup
                x_v
                (
                  fun
                    x_v_
                      :
                        Dependent_Sum
                          A
                          (fun a : A => Function (B a) (W_type A B))
                  =>
                    Dependent_Sum.matching
                      (
                        fun x_v
                        Dependent_Sum.matching_nodep@{s_i}
                          (
                            fun
                              (x_v_1 : A)
                              (fun x_v_2 : Function (B x_v_1) (W_type A B))
                            =>
                              Dependent_Function.abstract
                                (
                                  fun x_v_2_x : B x_v_1 =>
                                    P (Function.apply x_v_2 x_v_2_x)
                                )
                          )
                          x_v
                      )
                    x_v
                )
          )
          x
