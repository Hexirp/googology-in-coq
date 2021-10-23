(** 否定の型です。 *)

Require Googology_In_Coq.Base.Base.
Require Googology_In_Coq.Base.Void.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を開きます。 *)

Definition T (A : Type) : Type := A -> Void.T.
(* from: originally defined by Hexirp *)

(** 主型です。 *)

Definition map {A : Type} {B : Type} (f : A -> B)
  : T B -> T A
  := fun (nb : T B) (a : A) => nb (f a)
.
(* from: originally defined by Hexirp *)

(** 否定の型での写像です。 *)

Definition double_negation_introduce {A : Type}
  : A -> T (T A)
  := fun (a : A) (na : T A) => na a
.
(* from: originally defined by Hexirp *)

(** 二重否定の導入です。 *)

Definition three_negation_one {A : Type}
  : T (T (T A)) -> T A
  := map double_negation_introduce
.
(* from: originally defined by Hexirp *)

(** 三重否定を一重の否定に変換します。 *)
