(** 道での等式推論に関するモジュールです。 *)

Require Googology_In_Coq.Base.Base.
Require Googology_In_Coq.Base.Path.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を開きます。 *)

Definition walk
    {A : Type}
    (old_start_term : A)
    (new_start_term : A)
    {goal_term : A}
    (step : Path.T old_start_term new_start_term)
    (rest : Path.T new_start_term goal_term)
  : Path.T old_start_term goal_term
  := Path.conc step rest
.
(* from: originally defined by Hexirp *)

(** 1 ステップ分先に進みます。 *)

Definition arrive
  {A : Type}
  (goal_term : A)
  : Path.T goal_term goal_term
  := Path.id
.
(* from: originally defined by Hexirp *)

(** 終了します。 *)
