(** 空型に関するモジュールです。 *)

Require Googology_In_Coq.Base.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.

(** ライブラリを開きます。 *)

Inductive Void@{i | } : Type@{i} := .
(* from: originally defined by Hexirp *)

(** 空型です。 *)

Definition
  matching@{i | } (P : Void@{i} -> Type@{i}) : forall x : Void, P x
    := fun x : Void => match x with end
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  matching_nodep@{i | } (P : Type@{i}) : Void@{i} -> P
    := matching (fun x_ : Void => P)
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  absurd@{i | } (A : Type@{i}) : Void@{i} -> A
    := fun x : Void => matching_nodep A x
.
(* from: originally defined by Hexirp *)

(** 爆発律の関数です。 *)
