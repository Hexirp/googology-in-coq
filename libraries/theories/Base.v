(** Base モジュールは、基本的な設定を行なう場所です。 *)

(** [ltac_plugin] を読み込みます。 *)

Declare ML Module "ltac_plugin".

(** 対話証明の形式を [Classic] にします。 *)

Global Set Default Proof Mode "Classic".

(** 目標を選ぶ方法を [!] にします。 *)

Global Set Default Goal Selector "!".

(** [Elimination Schemes] を無効にします。 *)

Global Unset Elimination Schemes.

(** [Universe Polymorphism] を有効にします。 *)

Global Set Universe Polymorphism.

(** [Polymorphic Inductive Cumulativity] を有効にします。 *)

Global Set Polymorphic Inductive Cumulativity.

(** 宇宙の詳細を表示するようにします。 *)

Global Set Printing Universes.

(** [forall _ : x, y] の糖衣構文として [x -> y] を定義します。 https://github.com/coq/coq/blob/aaa8c94362b9159b1fa00baff8cd50cdc2972c7f/theories/Init/Notations.v#L15 を参照しています。 *)

Notation "x -> y" := ( forall _ : x, y ) ( at level 99, right associativity, y at level 200 ).
