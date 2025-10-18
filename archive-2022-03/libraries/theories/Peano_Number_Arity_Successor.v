(** 自然数の型のベータの [succ] に関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Unit.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Unit (Unit).

(** ライブラリを開きます。 *)

Inductive
  Peano_Number_Arity_Successor@{i | } : Type@{i}
    := wrap : Unit@{i} -> Peano_Number_Arity_Successor
.
(* from: originally defined by Hexirp *)

(** 自然数の型のベータの [succ] です。 *)

Definition
  unwrap@{i | } : Peano_Number_Arity_Successor@{i} -> Unit@{i}
    :=
      fun x : Peano_Number_Arity_Successor@{i} =>
        match x with wrap x_v => x_v end
.
(* from: originally defined by Hexirp *)

(** 自然数の型のベータの [succ] です。 *)

Definition unit@{i | } : Peano_Number_Arity_Successor@{i} := wrap Unit.unit.
(* from: originally defined by Hexirp *)

(** 自然数の型のベータの [succ] の構築子です。 *)

Definition
  matching@{i | }
      (P : Peano_Number_Arity_Successor@{i} -> Type@{i})
      (constructor_unit : P unit)
    : forall x : Peano_Number_Arity_Successor@{i}, P x
    :=
      fun x : Peano_Number_Arity_Successor@{i} =>
        match x as x_ return P x_ with
          wrap x_v
            =>
              Unit.matching
                (fun x_v_ : Unit@{i} => P (wrap x_v_))
                constructor_unit
                x_v
        end
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  matching_nodep@{i | } (P : Type@{i}) (constructor_unit : P)
    : Peano_Number_Arity_Successor@{i} -> P
    :=
      matching
        (fun x_ : Peano_Number_Arity_Successor@{i} => P)
        constructor_unit
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  comatching_nodep@{i | } (P : Type@{i})
    : P -> Peano_Number_Arity_Successor@{i}
    := fun x : P => unit
.
(* from: originally defined by Hexirp *)

(** 余場合分けです。 *)
