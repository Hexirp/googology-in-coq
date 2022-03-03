(** 自然数の型のベータの [zero] に関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Void.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Void (Void).

(** ライブラリを開きます。 *)

Definition Zero@{i | } : Type@{i} := Void@{i}.
(* from: originally defined by Hexirp *)

(** 自然数の型のベータの [zero] です。 *)

Definition
  matching@{i | } (P : Zero@{i} -> Type@{i}) : forall x : Zero@{i}, P x
    := Void.matching P
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  matching_nodep@{i | } (P : Type@{i}) : Zero@{i} -> P
    := matching (fun x_ : Zero@{i} => P)
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)
