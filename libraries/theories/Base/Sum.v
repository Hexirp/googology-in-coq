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
