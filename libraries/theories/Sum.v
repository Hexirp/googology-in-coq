(** 直和型に関するモジュールです。 *)

Require Googology_In_Coq.Base.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.

(** ライブラリを開きます。 *)

Inductive
  Sum@{i | } (A : Type@{i}) (B : Type@{i}) : Type@{i}
    := left : A -> Sum A B | right : B -> Sum A B
.
(* from: originally defined by Hexirp *)

(** 直和型です。 *)

Definition
  matching@{i | }
      (A : Type@{i})
      (B : Type@{i})
      (P : Sum@{i} A B -> Type@{i})
      (constructor_left : forall x_L : A, P (left A B x_L))
      (constructor_right : forall x_R : B, P (right A B x_R))
    : forall x : Sum A B, P x
    :=
      fun x : Sum A B =>
        match x as x_ return P x_ with
            left _ _ x_L => constructor_left x_L
          |
            right _ _ x_R => constructor_right x_R
        end
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  matching_nodep@{i | }
      {A : Type@{i}}
      {B : Type@{i}}
      {P : Type@{i}}
      (constructor_left : A -> P)
      (constructor_right : B -> P)
    : Sum A B -> P
    := matching A B (fun x_ : Sum A B => P) constructor_left constructor_right
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  map@{i | }
      (A : Type@{i})
      (B : Type@{i})
      (C : Type@{i})
      (D : Type@{i})
      (f : A -> C)
      (g : B -> D)
    : Sum@{i} A B -> Sum@{i} C D
    :=
      matching_nodep
        A
        B
        (Sum@{i} A B)
        (fun x_L : A => left C D (f x_L))
        (fun x_R : B => right C D (g x_R))
.
(* from: originally defined by Hexirp *)

(** 直和型の写像です。 *)
