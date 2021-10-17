(** 点ごとの道での等式推論です。 *)

Require Googology_In_Coq.Base.Base.
Require Googology_In_Coq.Base.Pointwise_Path.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を開きます。 *)

Definition walk
    {A B : Type}
    (old_start_term : A -> B)
    (new_start_term : A -> B)
    {goal_term : A -> B}
    (step : Pointwise_Path.T A B old_start_term new_start_term)
    (rest : Pointwise_Path.T A B new_start_term goal_term)
  : Pointwise_Path.T A B old_start_term goal_term
  := Pointwise_Path.conc step rest
.
(* from: originally defined by Hexirp *)

(** 1 ステップ分先に進みます。 *)

Definition arrive
  {A B : Type}
  (goal_term : A -> B)
  : Pointwise_Path.T A B goal_term goal_term
  := Pointwise_Path.id
.
(* from: originally defined by Hexirp *)

(** 終了します。 *)
