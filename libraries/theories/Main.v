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

(** trpt1_A0_lam_x_C_f_x_p_y です。 *)
(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L893 *)
Definition trpt1_A0_lam_x_B_f_x_p_y@{i0 i1 j | }
  (A0 : Type@{i0}) (A1 : Type@{i1}) (B : A1 -> Type@{j}) (f : A0 -> A1)
  {x x' : A0} (p : Path@{i0} x x') (y : B (f x))
  : Path@{j}
    (trpt1 A0 (fun x : A0 => B (f x)) p y)
    (trpt1 A1 B (ap f p) y).
Proof.
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** trptD_A0_lam_x_C_f_x_p_y です。 *)
(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L893 *)
Definition trptD_A0_lam_x_B_f_x_p_y@{i0 i1 j | }
  (A0 : Type@{i0}) (A1 : Type@{i1}) (B : A1 -> Type@{j}) (f : A0 -> A1)
  {x x' : A0} (p : Path@{i0} x x') (y : B (f x))
  : Path@{j}
    (trptD A0 (fun x : A0 => B (f x)) p y)
    (trptD A1 B (ap f p) y)
  := trpt1_A0_lam_x_B_f_x_p_y A0 A1 B f p y.

(** trptDD_A0_lam_x_B_f_x_lam_x_C_f_x_p_y_z です。 *)
(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L900 *)
Definition trptDD_A0_lam_x_B_f_x_lam_x_C_f_x_p_y_z@{i0 i1 j k | }
  (A0 : Type@{i0}) (A1 : Type@{i1}) (B : A1 -> Type@{j})
  (C : forall x : A1, B x -> Type@{k}) (f : A0 -> A1)
  {x x' : A0} (p : Path@{i0} x x') (y : B (f x)) (z : C (f x) y)
  : Path@{k}
    (trptDD A0 (fun x : A0 => B (f x)) (fun x : A0 => C (f x)) p y z)
    (trptD
      (B (f x'))
      (C (f x'))
      (inv (trptD_A0_lam_x_B_f_x_p_y A0 A1 B f p y))
      (trptDD A1 B C (ap f p) y z)).
Proof.
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** trptD_B_x'_C_x'_apD_f_p_trptDD_A_B_C_p_f_x_y です。 *)
(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L909 *)
Definition trptD_B_x'_C_x'_apD_f_p_trptDD_A_B_C_p_f_x_y@{i j k | }
  (A : Type@{i}) (B : A -> Type@{j})
  (C : forall x : A, B x -> Type@{k}) (f : forall x : A, B x)
  {x x' : A} (p : Path@{i} x x') (y : C x (f x))
  : Path@{k}
    (trptD (B x') (C x') (apD f p) (trptDD A B C p (f x) y))
    (trptD A (fun x : A => C x (f x)) p y).
Proof.
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** trpt1_fun_B_C_lam_'f_'_Path_comp_f_g_'f_'_g_p_idpath です。 *)
(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L917 *)
Definition trpt1_fun_B_C_lam_'f_'_Path_comp_f_g_'f_'_g_p_1
  @{i j k mik mjk | j <= mjk, k <= mjk, i <= mik, k <= mik}
  {A : Type@{i}} {B : Type@{j}} {C : Type@{k}}
  (f f' : B -> C) (g : A -> B) (p : Path@{mjk} f f')
  : Path@{mik}
    (trpt1
      (B -> C)
      (fun f_ : B -> C => Path@{mik} (comp f g) (comp f_ g))
      p
      (idpath (comp f g)))
    (ap (fun f_ => comp f_ g) p).
Proof.
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** trpt1_A_lam_x_B_idmap_x_p_y です。 trpt1_A0_lam_x_B_f_x_p_y の [f] を [idmap] としたものと解釈できます。 *)
(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L925 *)
Definition trpt1_A_lam_x_B_idmap_x_p_y@{i j sj | j < sj}
  (A : Type@{i}) (B : A -> Type@{j})
  {x x' : A} (p : Path@{i} x x') (y : B x)
  : Path@{j}
    (trpt1 A (fun x : A => B (idmap x)) p y)
    (trpt1 Type@{j} idmap@{sj} (ap B p) y).
Proof.
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** trpt1_A1_B_x0'_p1_trpt1_A0_lam_'x0_'_B_'x0_'_x1_p0_y です。 *)
(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L941 *)
Definition trpt1_A1_B_x0'_p1_trpt1_A0_lam_'x0_'_B_'x0_'_x1_p0_y@{i0 i1 j | }
  (A0 : Type@{i0}) (A1 : Type@{i1}) (B : A0 -> A1 -> Type@{j})
  {x0 x0' : A0} (p0 : Path@{i0} x0 x0') {x1 x1' : A1} (p1 : Path@{i1} x1 x1')
  (y : B x0 x1)
  : Path@{j}
    (trpt1 A1 (B x0') p1 (trpt1 A0 (fun x0_ : A0 => B x0_ x1) p0 y))
    (trpt1 A0 (fun x0_ : A0 => B x0_ x1') p0 (trpt1 A1 (B x0) p1 y)).
Proof.
  refine (match p1 with idpath => _ end).
  refine (match p0 with idpath => _ end).
  cbv.
  exact idpath.
Defined.
