(** 自然数の型に関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.W_type.
Require Googology_In_Coq.Peano_Number.Alpha.
Require Googology_In_Coq.Peano_Number.Beta.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.W_type (W_type).
Import Googology_In_Coq.Peano_Number.Alpha (Alpha).
Import Googology_In_Coq.Peano_Number.Beta (Beta).

(** ライブラリを開きます。 *)

Definition
  Peano_Number@{i s_i | i < s_i} : Type@{i}
    := W_type@{i} Alpha@{i} Beta@{i s_i}
.
(* from: originally defined by Hexirp *)

(** 自然数の型です。 *)

Definition
  zero@{i s_i | i < s_i} : Peano_Number@{i s_i}
    :=
      W_type.sup
        Alpha@{i}
        Beta@{i s_i}
        (
          W_type.Alpha.pair
            W_type.Beta@{i}
            W_type@{i}
            Alpha@{i}
            Beta@{i s_i}
            Alpha.zero
            (Beta.zero Peano_Number@{i s_i})
        )
.
(* from: originally defined by Hexirp *)

(** 自然数の型の第一構築子です。 *)

Definition
  succ@{i s_i | i < s_i} (n_p : Peano_Number@{i s_i}) : Peano_Number@{i s_i}
    :=
      W_type.sup
        Alpha@{i}
        Beta@{i s_i}
        (
          W_type.Alpha.pair
            W_type.Beta@{i}
            W_type@{i}
            Alpha@{i}
            Beta@{i s_i}
            Alpha.succ
            (Beta.succ Peano_Number@{i s_i} n_p)
        )
.
(* from: originally defined by Hexirp *)

(** 自然数の型の第二構築子です。 *)

Definition
  matching@{i s_i | i < s_i}
      (P : Peano_Number@{i s_i} -> Type@{i})
      (constructor_zero : P zero@{i s_i})
      (
        constructor_succ
          : forall x_p : Peano_Number@{i s_i}, P (succ@{i s_i} x_p)
      )
    : forall x : Peano_Number@{i s_i}, P x
.
Proof.
  refine (W_type.matching Alpha@{i} Beta@{i s_i} P _).
  refine
    (
      W_type.Alpha.matching
        W_type.Beta@{i}
        W_type@{i}
        Alpha@{i}
        Beta@{i s_i}
        (
          fun
            x_v_
              :
                W_type.Alpha@{i}
                  W_type.Beta@{i}
                  W_type@{i}
                  Alpha@{i}
                  Beta@{i s_i}
          =>
            P (W_type.sup Alpha@{i} Beta@{i s_i} x_v_)
        )
        _
    )
  .
  refine
    (
      Alpha.matching
        (
          fun x_v_a_ : Alpha@{i} =>
            forall
              x_v_b : W_type.Beta@{i} W_type@{i} Alpha@{i} Beta@{i s_i} x_v_a_
            ,
              P
                (
                  W_type.sup
                    Alpha@{i}
                    Beta@{i s_i}
                    (
                      Alpha.pair
                        W_type.Beta@{i}
                        W_type@{i}
                        Alpha@{i}
                        Beta@{i s_i}
                        x_v_a_
                        x_v_b
                    )
                )
        )
        _
        _
    )
  .
  -
    exact _.
  -
    exact _.
Defined.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  induction@{i s_i | i < s_i}
      (P : Peano_Number@{i s_i} -> Type@{i})
      (constructor_zero : P zero@{i s_i})
      (
        constructor_succ
          : forall x_p : Peano_Number@{i s_i}, P x_p -> P (succ@{i s_i} x_p)
      )
    : forall x : Peano_Number@{i s_i}, P x
    := _
.
(* from: originally defined by Hexirp *)

(** 帰納法の原理です。 *)
