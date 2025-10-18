(** 論理等価に関するモジュールです。 *)

Require Googology_In_Coq.Base.Base.
Require Googology_In_Coq.Base.Product.

(** [Googology_In_Coq.Base.Base] を要求します。 *)

Import Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を開きます。 *)

Definition T (A : Type) (B : Type) : Type
  := Product.T (A -> B) (B -> A)
.
(* from: originally defined by Hexirp *)

(** 主型です。 *)

Definition left {A : Type} {B : Type} : T A B -> A -> B
  := Product.first
.
(* from: originally defined by Hexirp *)

(** 左から右への関数を取り出す。 *)

Definition right {A : Type} {B : Type} : T A B -> B -> A
  := Product.second
.
(* from: originally defined by Hexirp *)

(** 右から左への関数を取り出す。 *)
