(** 型の型です。 *)

Require Googology_In_Coq.Base.Base.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を開きます。 *)

Definition T : Type := Type.
(* from: originally defined by Hexirp *)

(** 主型です。 *)

Definition of {A : Type}
  : A -> Type
  := fun x : A => A
.
(* from: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/ *)

(** 値の型です。 *)
