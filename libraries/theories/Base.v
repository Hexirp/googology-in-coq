(** [Googology_In_Coq.Base] は基本的な設定を与えます。 *)

Declare ML Module "ltac_plugin".

(** [ltac_plugin] を読み込みます。 *)

Declare ML Module "ssrmatching_plugin".

(** [ssrmatching_plugin] を読み込みます。 *)

Declare ML Module "ssreflect_plugin".

(** [ssreflect_plugin] を読み込みます。 *)

Global Set Default Proof Mode "Classic".

(** 対話的な証明を行う時のモードを [Classic] にセットします。 *)

Global Set Default Goal Selector "all".

(** ゴールのセレクタのデフォルトを [all] にします。 *)

Global Unset Elimination Schemes.

(** [Elimination Schemes] をオフにします。 *)

Global Set Universe Polymorphism.

(** [Universe Polymorphism] をオンにします。 *)

Global Set Polymorphic Inductive Cumulativity.

(** [Polymorphic Inductive Cumulativity] をオンにします。 *)

Notation "x -> y"
  := (forall (_ : x), y)
  (at level 99, right associativity, y at level 200)
.

(** [forall (_ : x), y] の糖衣構文として [x -> y] を定義します。 *)
