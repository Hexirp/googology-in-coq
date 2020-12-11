(* Run with -nois. *)

(** * 開発中のライブラリ *)

(** 必要なライブラリをインポートします。 *)
Require Import GiC.Base.
Require Import GiC.Path.Base.
Require Import GiC.Path.Fibration.

(** 帰納原理 (induction principle) を生成しないように設定します。 *)
Unset Elimination Schemes.

(** 宇宙多相 (universe polymorphism) について設定します。 *)
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

(** 宇宙 (universe) について表示するように設定します。 *)
Set Printing Universes.

(** タクティックが使用できるように設定します。 *)
Set Default Proof Mode "Classic".

(** ビュレットを使用しないときにエラーになるように設定します。 *)
Set Default Goal Selector "!".

(** apD_f_p です。 *)
(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L953 *)
Definition apD_f_p@{i j | }
  {A : Type@{i}} {B : Type@{j}} {x y : A} (p: Path@{i} x y) (f : A -> B)
  : Path@{j} (apD f p) (conc (trpt1_A_lam_x_B_p_u p (f x)) (ap f p)).
Proof.
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.
