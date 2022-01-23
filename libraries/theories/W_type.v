(** ウ型に関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Dependent_Function.
Require Googology_In_Coq.Function.
Require Googology_In_Coq.W_type.Alpha.
Require Googology_In_Coq.W_type.Beta.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Dependent_Function (Dependent_Function).
Import Googology_In_Coq.Function (Function).
Import Googology_In_Coq.W_type.Alpha (Alpha).
Import Googology_In_Coq.W_type.Beta (Beta).

(** ライブラリを開きます。 *)

Inductive
  W_type@{i | } (A : Type@{i}) (B : A -> Type@{i}) : Type@{i}
    := sup : Alpha Beta W_type A B -> W_type A B
.
(* from: originally defined by Hexirp *)

(** ウ型です。 W-types です。 *)

Definition
  matching@{i | }
      (A : Type@{i})
      (B : A -> Type@{i})
      (P : W_type A B -> Type@{i})
      (
        constructor_sup
          : forall x_v : Alpha Beta W_type A B, P (sup A B x_v)
      )
    : forall x : W_type A B, P x
    :=
      fun x : W_type A B =>
        match x as x_ return P x_ with sup _ _ x_v => constructor_sup x_v end
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  matching_nodep@{i | }
      (A : Type@{i})
      (B : A -> Type@{i})
      (P : Type@{i})
      (constructor_sup : Alpha Beta W_type A B -> P)
    : W_type A B -> P
    := matching A B (fun x_ : W_type A B => P) constructor_sup
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  induction@{i | }
      (A : Type@{i})
      (B : A -> Type@{i})
      (P : W_type A B -> Type@{i})
      (
        constructor_sup
          :
            forall
              x_v : Alpha Beta W_type A B
            ,
              (
                forall x_v_2_x : B (Alpha.first Beta W_type A B x_v),
                  P
                    (
                      Beta.apply
                        W_type
                        A
                        B
                        (Alpha.first Beta W_type A B x_v)
                        (Alpha.second Beta W_type A B x_v)
                        x_v_2_x
                    )
              )
            ->
              P (sup A B x_v)
      )
    : forall x : W_type A B, P x
    :=
      fix induction (x : W_type A B) {struct x} : P x :=
        matching
          A
          B
          P
          (
            fun
              x_v : Alpha Beta W_type A B
            =>
              constructor_sup
                x_v
                (
                  fun x_v_2_x : B (Alpha.first Beta W_type A B x_v) =>
                    induction
                      (
                        Beta.apply
                          W_type
                          A
                          B
                          (Alpha.first Beta W_type A B x_v)
                          (Alpha.second Beta W_type A B x_v)
                          x_v_2_x
                      )
                )
          )
          x
.
(* from: originally defined by Hexirp *)

(** 帰納法の原理です。 *)

Definition
  recursion@{i | }
      (A : Type@{i})
      (B : A -> Type@{i})
      (P : Type@{i})
      (
        constructor_sup
          :
            forall
              x_v : Alpha Beta W_type A B
            ,
              (B (Alpha.first Beta W_type A B x_v) -> P)
            ->
              P
      )
    : W_type A B -> P
    := induction A B (fun x_ => P) constructor_sup
.
(* from: originally defined by Hexirp *)

(** 再帰です。 *)

Definition
  map@{i | }
      (A : Type@{i})
      (B : A -> Type@{i})
      (C : Type@{i})
      (D : C -> Type@{i})
      (f : A -> C)
      (g : forall x : A, D (f x) -> B x)
    : W_type A B -> W_type C D
    :=
      recursion
        A
        B
        (W_type C D)
        (
          fun
            (x_v : Alpha Beta W_type A B)
            (y : B (Alpha.first Beta W_type A B x_v) -> W_type C D)
          =>
            sup
              C
              D
              (
                Alpha.pair
                  Beta
                  W_type
                  C
                  D
                  (f (Alpha.first Beta W_type A B x_v))
                  (
                    fun z : D (f (Alpha.first Beta W_type A B x_v x_v)) =>
                      y (g (Alpha.first Beta W_type A B x_v x_v) z)
                  )
              )
        )
.
(* from: originally defined by Hexirp *)

(** ウ型の写像です。 *)
