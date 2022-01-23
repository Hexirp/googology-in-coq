(** 超型です。 *)

Require Googology_In_Coq.Base.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.

(** ライブラリを開きます。 *)

Definition Universe@{i s_i | i < s_i} : Type@{s_i} := Type@{i}.
(* from: originally defined by Hexirp *)

(** 超型です。 *)
