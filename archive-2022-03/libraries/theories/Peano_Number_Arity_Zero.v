(** 自然数の型のベータの [zero] に関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Void.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Void (Void).

(** ライブラリを開きます。 *)

Inductive
  Peano_Number_Arity_Zero@{i | } : Type@{i}
    := wrap : Void@{i} -> Peano_Number_Arity_Zero
.
(* from: originally defined by Hexirp *)

(** 自然数の型のベータの [zero] です。 *)

Definition
  unwrap@{i | } : Peano_Number_Arity_Zero@{i} -> Void@{i}
    := fun x : Peano_Number_Arity_Zero@{i} => match x with wrap x_v => x_v end
.
(* from: originally defined by Hexirp *)

(** 自然数の型のベータの [zero] です。 *)

Definition
  matching@{i | } (P : Peano_Number_Arity_Zero@{i} -> Type@{i})
    : forall x : Peano_Number_Arity_Zero@{i}, P x
    :=
      fun x : Peano_Number_Arity_Zero@{i} =>
        match x as x_ return P x_ with
          wrap x_v => Void.matching (fun x_v_ : Void@{i} => P (wrap x_v_)) x_v
        end
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  matching_nodep@{i | } (P : Type@{i}) : Peano_Number_Arity_Zero@{i} -> P
    := matching (fun x_ : Peano_Number_Arity_Zero@{i} => P)
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)
