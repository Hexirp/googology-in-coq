(** 直和型に関するモジュールです。 *)

Require Googology_In_Coq.Base.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.

(** ライブラリを開きます。 *)

Inductive Sum@{i | } (A : Type@{i}) (B : Type@{i}) : Type@{i}
  := left : A -> T A B | right : B -> T A B
.
(* from: originally defined by Hexirp *)

(** 直和型です。 *)

Arguments left {A} {B} a.

(** [left] の暗黙引数を設定します。 *)

Arguments right {A} {B} b.

(** [right] の暗黙引数を設定します。 *)

Definition matching@{i | }
    {A : Type@{i}}
    {B : Type@{i}}
    (P : Sum A B -> Type@{i})
    (construct_left : forall x_L : A, P (left x_L))
    (construct_right : forall x_R : B, P (right x_R))
  : forall x : Sum A B, P x
  :=
    fun x : Sum A B =>
      match x with
          left x_L => construct_left x_L
        |
          right x_R => construct_right x_R
      end
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition matching_nodep@{i | }
    {A : Type@{i}}
    {B : Type@{i}}
    {P : Type@{i}}
    (construct_left : A -> P)
    (construct_right : B -> P)
  : Sum A B -> P
  := matching (fun x_ : Sum A B => P) construct_left construct_right
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)
