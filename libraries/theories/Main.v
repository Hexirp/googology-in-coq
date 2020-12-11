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

(** apD_comp_f_g_p です。 *)
(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L959 *)
Definition apD_comp_f_g_p@{i0 i1 j | }
  (A0 : Type@{i0}) (A1 : Type@{i1}) (B : A1 -> Type@{j})
  (f : forall x : A1, B x) (g : A0 -> A1) {x x' : A0} (p : Path@{i0} x x')
  : Path@{j}
    (apD (fun x_ : A0 => f (g x_)) p)
    (conc (trpt1_A0_lam_x_B_f_x_p_y A0 A1 B g p (f (g x))) (apD f (ap g p))).
Proof.
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.
