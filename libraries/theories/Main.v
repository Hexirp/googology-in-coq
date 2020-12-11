(* Run with -nois. *)

(** * 開発中のライブラリ *)

(** 必要なライブラリをインポートします。 *)
Require Import GiC.Base.
Require Import GiC.Function.
Require Import GiC.Path.Base.
Require Import GiC.Path.Function.
Require Import GiC.Path.OneDim.
Require Import GiC.Path.Transposition.
Require Import GiC.Path.Transport.

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

(** ** [trpt2] に関する定理 *)

(** trpt2_A_B_q_y です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L793 *)
Definition trpt2_A_B_q_y@{i j | }
  {A : Type@{i}} (B : A -> Type@{j})
  {x x' : A} {p p' : Path@{i} x x'} (q : Path@{i} p p')
  (y : B x)
  : Path@{j} (trpt2 A B q y) (ap10 (ap (trpt1 A B) q) y).
Proof.
  refine (match q with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** trpt2_A_B_conc_q0_q1_y です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L798 *)
Definition trpt2_A_B_cq0q1_y@{i j | }
  {A : Type@{i}} (B : A -> Type@{j})
  {x x' : A} {p p' p'' : Path@{i} x x'}
  (q0 : Path@{i} p p') (q1 : Path@{i} p' p'')
  (y : B x)
  : Path@{j}
    (trpt2 A B (conc q0 q1) y)
    (conc (trpt2 A B q0 y) (trpt2 A B q1 y)).
Proof.
  refine (match q1 with idpath => _ end).
  refine (match q0 with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** trpt2_A_B_inv_q_y です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L805 *)
Definition trpt2_A_B_vq_y@{i j | }
  {A : Type@{i}} (B : A -> Type@{j})
  {x x' : A} {p p' : Path@{i} x x'} (q : Path@{i} p p')
  (y : B x)
  : Path@{j} (trpt2 A B (inv q) y) (inv (trpt2 A B q y)).
Proof.
  refine (match q with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** conc_ap_trpt1_A_B_p_r_trpt2_A_B_q_y' です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L810 *)
Definition conc_ap_trpt1_A_B_p_r_trpt2_A_B_q_y'@{i j | }
  {A : Type@{i}} (B : A -> Type@{j})
  {x x' : A} {p p' : Path@{i} x x'} (q : Path@{i} p p')
  {y y' : B x} (r : Path@{j} y y')
  : Path@{j}
    (conc (ap (trpt1 A B p) r) (trpt2 A B q y'))
    (conc (trpt2 A B q y) (ap (trpt1 A B p') r)).
Proof.
  refine (match q with idpath => _ end).
  simpl trpt2.
  refine_conc (ap (trpt1 A B p) r).
  -
    exact (conc_p_1 (ap (trpt1 A B p) r)).
  -
    exact (inv (conc_1_p (ap (trpt1 A B p) r))).
Defined.

(** ** [apD] に関する定理 *)

(** apD_f_idpath です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L372 *)
Definition apD_f_1@{i j | }
  {A : Type@{i}} {B : A -> Type@{j}} (f : forall x : A, B x) (x : A)
  : Path@{j} (apD f (idpath x)) (idpath (f x)).
Proof.
  cbv.
  exact idpath.
Defined.

(** apD_f_conc_p_q です。 *)
(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L860 *)
Definition apD_f_cpq@{i j | }
  {A : Type@{i}} {B : A -> Type@{j}} (f : forall x : A, B x)
  {x y z : A} (p : Path@{i} x y) (q : Path@{i} y z)
  : Path@{j}
    (apD f (conc p q))
    (conc (conc (trpt_cpq_u B p q (f x)) (ap (trpt q) (apD f p))) (apD f q)).
Proof.
  refine (match q with idpath => _ end).
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** apD_f_inv_p です。 *)
(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L868 *)
Definition apD_f_vp@{i j | }
  {A : Type@{i}} {B : A -> Type@{j}} (f : forall x : A, B x)
  {x y : A} (p : Path@{i} x y)
  : Path@{j}
    (apD f (inv p))
    (path_trpt_vp_u_v B p (f y) (f x) (inv (apD f p))).
Proof.
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** ** 特殊な fibration の上での輸送 *)

(** trpt1_A_lam_x_B_p_u です。 *)
(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L881 *)
Definition trpt1_A_lam_x_B_p_u@{i j | }
  {A : Type@{i}} {B : Type@{j}} {x x' : A} (p : Path@{i} x x') (u : B)
  : Path@{j} (trpt1 A (fun x : A => B) p u) u.
Proof.
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** conc_trpt2_A_lam_x_B_q_u_'trpt1_A_lam_x_B_p_u'_p'_u です。 *)
(* from: invert https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L881 *)
Definition conc_trpt2_A_lam_x_B_q_u_'trpt1_A_lam_x_B_p_u'_p'_u@{i j | }
  {A : Type@{i}} {B : Type@{j}}
  {x x' : A} (p p' : Path@{i} x x') (q : Path@{i} p p') (u : B)
  : Path@{j}
    (conc (trpt2 A (fun x : A => B) q u) (trpt1_A_lam_x_B_p_u p' u))
    (trpt1_A_lam_x_B_p_u p u).
Proof.
  refine (match q with idpath => _ end).
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** trptD_A_lam_x_C_f_x_p_y です。 *)
(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L893 *)
Definition trptD_A_lam_x_C_f_x_p_y@{i j k | }
  (A : Type@{i}) (B : Type@{j}) (C : B -> Type@{k}) (f : A -> B)
  {x x' : A} (p : Path@{i} x x') (y : C (f x))
  : Path@{k}
    (trptD A (fun x : A => C (f x)) p y)
    (trptD B C (ap f p) y).
Proof.
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.
