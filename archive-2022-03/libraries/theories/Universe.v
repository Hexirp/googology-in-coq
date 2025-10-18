(** 超型です。 *)

Require Googology_In_Coq.Base.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.

(** ライブラリを開きます。 *)

Inductive
  Universe@{i s_i | i < s_i} : Type@{s_i} := wrap : Type@{i} -> Universe
.
(* from: originally defined by Hexirp *)

(** 超型です。 *)

Definition
  unwrap@{i s_i | i < s_i} : Universe@{i s_i} -> Type@{i}
    := fun x : Universe@{i s_i} => match x with wrap x_v => x_v end
.
(* from: originally defined by Hexirp *)

(** 超型です。 *)
