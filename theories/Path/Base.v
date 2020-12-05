(* Run with -nois. *)

(** * GiC.Path.Base *)

(** [GiC.Path.Base] は道に関する基本的な定義を提供します。

    具体的には、よく現れるパターンを一般化したタクティックや、 [GiC.Base] にある関数のバリエーションなどを提供します。
 *)

(** 必要なライブラリをインポートします。 *)
Require Import GiC.Base.

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

(** ** 汎用的な関数の定義 *)

(** 一変数関数に対する ap です。 *)
(* from: originally defined by Hexirp *)
Definition ap1@{i j | }
  {A : Type@{i}} {B : Type@{j}} (f : A -> B) {x x' : A} (p : Path@{i} x x')
  : Path@{j} (f x) (f x')
  := ap f p.

(** 二変数関数に対する ap です。 *)
(* from: originally defined by Hexirp *)
Definition ap2@{i j k | }
  {A : Type@{i}} {B : Type@{j}} {C : Type@{k}} (f : A -> B -> C)
  {x x' : A} (p : Path@{i} x x') {y y' : B} (q : Path@{j} y y')
  : Path@{k} (f x y) (f x' y')
  := match p with idpath => ap1 (f x) q end.

(** 三変数関数に対する ap です。 *)
(* from: originally defined by Hexirp *)
Definition ap3@{i j k l | }
  {A : Type@{i}} {B : Type@{j}} {C : Type@{k}} {D : Type@{l}}
  (f : A -> B -> C -> D)
  {x x' : A} (p : Path@{i} x x')
  {y y' : B} (q : Path@{j} y y')
  {z z' : C} (r : Path@{k} z z')
  : Path@{l} (f x y z) (f x' y' z')
  := match p with idpath => ap2 (f x) q r end.
