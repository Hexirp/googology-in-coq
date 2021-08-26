(** ボトムの型に関するモジュールです。 *)

Require Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を要求します。 *)

Import Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を開きます。 *)

Inductive T
  : Type
  :=
.
(* from: originally defined by Hexirp *)

(** 主型です。 *)

Definition absurd {A : Type}
  : T -> A
  := fun x => match x with end
.
(* from: originally defined by Hexirp *)

(** 矛盾による証明です。 *)
