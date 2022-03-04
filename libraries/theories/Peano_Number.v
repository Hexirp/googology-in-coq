(** 自然数の型に関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.W_type_Alpha.
Require Googology_In_Coq.W_type_Beta.
Require Googology_In_Coq.W_type.
Require Googology_In_Coq.Path.
Require Googology_In_Coq.Peano_Number_Alpha.
Require Googology_In_Coq.Peano_Number_Beta.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.W_type_Alpha (W_type_Alpha).
Import Googology_In_Coq.W_type_Beta (W_type_Beta).
Import Googology_In_Coq.W_type (W_type).
Import Googology_In_Coq.Path (Path).
Import Googology_In_Coq.Peano_Number_Alpha (Peano_Number_Alpha).
Import Googology_In_Coq.Peano_Number_Beta (Peano_Number_Beta).

(** ライブラリを開きます。 *)

Definition
  Peano_Number@{i s_i | i < s_i} : Type@{i}
    := W_type@{i} Peano_Number_Alpha@{i} Peano_Number_Beta@{i s_i}
.
(* from: originally defined by Hexirp *)

(** 自然数の型です。 *)

Definition
  zero@{i s_i | i < s_i} : Peano_Number@{i s_i}
    :=
      W_type.fixer
        Peano_Number_Alpha@{i}
        Peano_Number_Beta@{i s_i}
        (
          W_type_Alpha.pair
            W_type_Beta@{i}
            W_type@{i}
            Peano_Number_Alpha@{i}
            Peano_Number_Beta@{i s_i}
            Peano_Number_Alpha.zero
            (Peano_Number_Beta.zero Peano_Number@{i s_i})
        )
.
(* from: originally defined by Hexirp *)

(** 自然数の型の第一構築子です。 *)

Definition
  succ@{i s_i | i < s_i} (n_p : Peano_Number@{i s_i}) : Peano_Number@{i s_i}
    :=
      W_type.fixer
        Peano_Number_Alpha@{i}
        Peano_Number_Beta@{i s_i}
        (
          W_type_Alpha.pair
            W_type_Beta@{i}
            W_type@{i}
            Peano_Number_Alpha@{i}
            Peano_Number_Beta@{i s_i}
            Peano_Number_Alpha.succ
            (Peano_Number_Beta.succ Peano_Number@{i s_i} n_p)
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
  refine
    (W_type.matching Peano_Number_Alpha@{i} Peano_Number_Beta@{i s_i} P _)
  .
  refine
    (
      W_type_Alpha.matching
        W_type_Beta@{i}
        W_type@{i}
        Peano_Number_Alpha@{i}
        Peano_Number_Beta@{i s_i}
        (
          fun
            x_v_
              :
                W_type_Alpha@{i}
                  W_type_Beta@{i}
                  W_type@{i}
                  Peano_Number_Alpha@{i}
                  Peano_Number_Beta@{i s_i}
          =>
            P
              (
                W_type.fixer
                  Peano_Number_Alpha@{i}
                  Peano_Number_Beta@{i s_i}
                  x_v_
              )
        )
        _
    )
  .
  refine
    (
      Peano_Number_Alpha.matching
        (
          fun x_v_a_ : Peano_Number_Alpha@{i} =>
            forall
              x_v_b
                :
                  W_type_Beta@{i}
                    W_type@{i}
                    Peano_Number_Alpha@{i}
                    Peano_Number_Beta@{i s_i}
                    x_v_a_
            ,
              P
                (
                  W_type.fixer
                    Peano_Number_Alpha@{i}
                    Peano_Number_Beta@{i s_i}
                    (
                      W_type_Alpha.pair
                        W_type_Beta@{i}
                        W_type@{i}
                        Peano_Number_Alpha@{i}
                        Peano_Number_Beta@{i s_i}
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
    refine
      (
        fun
          x_v_b
            :
              W_type_Beta@{i}
                W_type@{i}
                Peano_Number_Alpha@{i}
                Peano_Number_Beta@{i s_i}
                Peano_Number_Alpha.zero
        =>
          _
      )
    .
    refine
      (
        Path.trpt
          (
              Peano_Number_Beta@{i s_i} Peano_Number_Alpha.zero
            ->
              Peano_Number@{i s_i}
          )
          (Peano_Number_Beta.zero Peano_Number@{i s_i})
          x_v_b
          (
            fun
              x_
                :
                    Peano_Number_Beta@{i s_i} Peano_Number_Alpha.zero
                  ->
                    Peano_Number@{i s_i}
            =>
              P
                (
                  W_type.fixer
                    Peano_Number_Alpha@{i}
                    Peano_Number_Beta@{i s_i}
                    (
                      W_type_Alpha.pair
                        W_type_Beta@{i}
                        W_type@{i}
                        Peano_Number_Alpha@{i}
                        Peano_Number_Beta@{i s_i}
                        Peano_Number_Alpha.zero
                        x_
                    )
                )
          )
          _
          _
      )
    .
    +
      Fail exact _.
      admit.
    +
      exact constructor_zero.
  -
    Fail exact _.
    admit.
Admitted.
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
.
Proof.
  Fail exact _.
  admit.
Admitted.
(* from: originally defined by Hexirp *)

(** 帰納法の原理です。 *)
