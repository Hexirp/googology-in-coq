(* Run with -nois. *)

(** * GiC.Path.Base *)

(** [GiC.Path.Base] は道に関する基本的な定義を提供します。

    具体的には、よく現れるパターンを一般化したタクティックなどを提供します。
 *)

(** 必要なライブラリをインポートします。 *)
Require Import GiC.Base GiC.Function.

(** 帰納原理 (induction principle) を生成しないように設定します。 *)
Unset Elimination Schemes.

(** 宇宙多相 (universe polymorphism) について設定します。 *)
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

(** 宇宙 (universe) について表示するように設定します。 *)
Set Printing Universes.

(** タクティックが使用できるように設定します。 *)
Set Default Proof Mode "Classic".

(** ** 汎用的なタクティックの定義 *)

(** [refine_conc t] は [Path x y -| Path x t, Path t y] です。 *)
Ltac refine_conc t := refine (@GiC.Base.conc@{_} _ _ t _ _ _).
