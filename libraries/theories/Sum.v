(** 直和の型に関するモジュールです。 *)

Require Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を要求します。 *)

Import Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を開きます。 *)

Inductive T (A : Type) (B : Type)
  : Type
  := left : A -> T A B | right : B -> T A B
.
(* from: originally defined by Hexirp *)

(** 主型です。 *)

Arguments left {A} {B} a.

(** [left] についての暗黙引数を設定します。 *)

Arguments right {A} {B} b.

(** [right] についての暗黙引数を設定します。 *)

Definition induction
    {A : Type}
    {B : Type}
    (P : T A B -> Type)
    (construct_left : forall x_L : A, P (left x_L))
    (construct_right : forall x_R : B, P (right x_R))
  : forall x : T A B, P x
  :=
    fun x : T A B =>
      match x with
          left x_L => construct_left x_L
        |
          right x_R => construct_right x_R
      end
.
(* from: originally defined by Hexirp *)

(** 帰納法です。 *)

Definition recursion
    {A : Type}
    {B : Type}
    {P : Type}
    (construct_left : A -> P)
    (construct_right : B -> P)
  : T A B -> P
  := induction (fun x_ : T A B => P) construct_left construct_right
.
(* from: originally defined by Hexirp *)

(** 再帰です。 *)
