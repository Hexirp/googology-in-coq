(** ペアノ式の自然数の型に関するモジュールです。 *)

Require Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を要求します。 *)

Import Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を開きます。 *)

Inductive T
  : Type
  := zero : T | succ : T -> T
.
(* from: originally defined by Hexirp *)

(** 主型です。 *)

Definition case_analysis
    (P : T -> Type)
    (construct_zero : P zero)
    (construct_succ : forall x_p : T, P (succ x_p))
  : forall x : T, P x
  :=
    fun x : T =>
      match x with
          zero => construct_zero
        |
          succ x_p => construct_succ x_p
      end
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition case_analysis_independent
    (P : Type)
    (construct_zero : P)
    (construct_succ : T -> P)
  : T -> P
  := case_analysis (fun x_ : T => P) construct_zero construct_succ
.
(* from: originally defined by Hexirp *)

(** 非依存型版の場合分けです。 *)

Definition induction
    (P : T -> Type)
    (construct_zero : P zero)
    (construct_succ : forall x_p : T, P x_p -> P (succ x_p))
  : forall x : T, P x
  :=
    fix inductiver (x : T) {struct x} : P x
      :=
        case_analysis
          P
          construct_zero
          (fun x_p : T => construct_succ x_p (inductiver x_p))
          x
.
(* from: originally defined by Hexirp *)

(** 帰納法です。 *)

Definition recursion
    {P : Type}
    (construct_zero : P)
    (construct_succ : T -> P -> P)
  : T -> P
  := induction (fun x_ : T => P) construct_zero construct_succ
.
(* from: originally defined by Hexirp *)

(** 再帰です。 *)

Definition iteration
    {P : Type}
    (construct_zero : P)
    (construct_succ : P -> P)
  : T -> P
  := recursion construct_zero (fun x_p : T => construct_succ)
.
(* from: originally defined by Hexirp *)

(** 繰り返しです。 *)
