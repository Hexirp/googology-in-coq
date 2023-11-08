(** Base モジュールは、基本的な設定を行ないます。 *)

Declare ML Module "ltac_plugin".

(** [ltac_plugin] を読み込みます。 *)

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

Global Set Printing Universes.

(** 宇宙階層を表示するようにします。 *)

Notation "x -> y" := ( forall _ : x, y ) ( at level 99, right associativity, y at level 200 ).

(** [forall _ : x, y] の糖衣構文として [x -> y] を定義します。 *)
