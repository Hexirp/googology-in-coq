(** 自然数の型に関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Sum.
Require Googology_In_Coq.Unit.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Sum (Sum).
Import Googology_In_Coq.Unit (Unit).

(** ライブラリを開きます。 *)

Inductive
  Peano_Number_Tag@{i | } : Type@{i}
    := wrap : Sum@{i} Unit@{i} Unit@{i} -> Peano_Number_Tag
.
(* from: originally defined by Hexirp *)

(** 自然数の型のアルファです。 *)

Definition
  unwrap@{i | } : Peano_Number_Tag@{i} -> Sum@{i} Unit@{i} Unit@{i}
    := fun x : Peano_Number_Tag@{i} => match x with wrap x_v => x_v end
.
(* from: originally defined by Hexirp *)

(** 自然数の型のアルファです。 *)

Definition
  zero@{i | } : Peano_Number_Tag@{i}
    := wrap (Sum.left Unit@{i} Unit@{i} Unit.unit)
.
(* from: originally defined by Hexirp *)

(** 自然数の型のアルファの第一構築子です。 *)

Definition
  successor@{i | } : Peano_Number_Tag@{i}
    := wrap (Sum.right Unit@{i} Unit@{i} Unit.unit)
.
(* from: originally defined by Hexirp *)

(** 自然数の型のアルファの第二構築子です。 *)

Definition
  matching@{i | }
      (P : Peano_Number_Tag@{i} -> Type@{i})
      (constructor_zero : P zero)
      (constructor_successor : P successor)
    : forall x : Peano_Number_Tag@{i}, P x
    :=
      fun x : Peano_Number_Tag@{i} =>
        match x as x_ return x_ with
          wrap x_v
            =>
              Sum.matching
                Unit@{i}
                Unit@{i}
                (fun x_v_ : Sum@{i} Unit@{i} Unit@{i} => P (wrap x_v_))
                (
                  fun x_v_L : Unit@{i} =>
                    Unit.matching
                      (
                        fun x_v_L_ : Unit@{i} =>
                          P (wrap (Sum.left Unit@{i} Unit@{i} x_v_L_))
                      )
                      constructor_zero
                )
                (
                  fun x_v_R : Unit@{i} =>
                    Unit.matching
                      (
                        fun x_v_R_ : Unit =>
                          P (wrap (Sum.right Unit@{i} Unit@{i} x_v_R_))
                      )
                      constructor_successor
                )
                x_v
        end
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  matching_nodep@{i | }
      (P : Type@{i})
      (constructor_zero : P)
      (constructor_successor : P)
  : Peano_Number_Tag@{i} -> P
  :=
    matching
      (fun x_ : Peano_Number_Tag@{i} => P)
      constructor_zero
      constructor_successor
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)
