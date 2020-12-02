(* Run with -nois. *)

(** * GiC.Function *)

(** GiC.Function は、関数に関する定義を提供します。

    具体的には、変数の抽象化と適用だけで表現できるような様々な高階関数と、それらに関わる単純な等式を提供します。
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

(** 依存関数に対応する [comp] です。 *)
(* from: originally defined by Hexirp *)
Definition compD@{i j k | } {A : Type@{i}} {B : Type@{j}} {C : B -> Type@{k}}
  : (forall b : B, C b) -> forall (g : A -> B) (a : A), C (g a)
  := fun f g x => f (g x).

(** 依存関数に対応する [apply] です。 *)
(* from: originally defined by Hexirp *)
Definition applyD@{i j | } {A : Type@{i}} {B : A -> Type@{j}}
  : (forall a : A, B a) -> forall (a : A), B a
  := fun f x => f x.
