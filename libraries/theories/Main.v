(* Run with -nois. *)

(** * 開発中のライブラリ *)

(** 必要なライブラリをインポートします。 *)
Require Import GiC.Base.
Require Import GiC.Path.Base.
Require Import GiC.Path.OneDim.
Require Import GiC.Path.Functoriality.

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

(** ** 高階での一貫性 (coherence) に関する定理 *)

(** conc2_ap_f_p_ap_g_p です。 *)
(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L984 *)
Definition conc2_ap_f_p_ap_g_p@{i j | }
  {A : Type@{i}} {B : Type@{j}}
  {x' y' z' : B} (f : A -> Path@{j} x' y') (g : A -> Path@{j} y' z')
  {x y : A} (p : Path@{i} x y)
  : Path@{j} (conc2 (ap f p) (ap g p)) (ap (fun x : A => conc (f x) (g x)) p).
Proof.
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** conc_'ap_f_cpq'_f_p_inv_p_conc_conc2_idpath_'ap_f_vp'_f_p_'conc_p_vp'_ap_f_p です。 *)
(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L999 *)
Definition
  conc_'ap_f_cpq'_f_p_vp_conc_conc2_1_'ap_f_vp'_f_p_'conc_p_vp'_ap_f_p@{i j | }
  {A : Type@{i}} {B : Type@{j}} (f : A -> B) {x y : A} (p : Path@{i} x y)
  : Path@{j}
    (conc
      (ap_f_cpq f p (inv p))
      (conc (conc2 idpath (ap_f_vp f p)) (conc_p_vp (ap f p))))
    (ap (ap f) (conc_p_vp p)).
Proof.
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** conc_'ap_f_cpq'_f_inv_p_p_conc_conc2_'ap_f_vp'_f_p_idpath_'conc_vp_p'_ap_f_p です。 *)
(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1006 *)
Definition
  conc_'ap_f_cpq'_f_vp_p_conc_conc2_'ap_f_vp'_f_p_1_'conc_vp_p'_ap_f_p@{i j | }
  {A : Type@{i}} {B : Type@{j}} (f : A -> B) {x y : A} (p : Path@{i} x y)
  : Path@{j}
    (conc
      (ap_f_cpq f (inv p) p)
      (conc (conc2 (ap_f_vp f p) idpath) (conc_vp_p (ap f p))))
    (ap (ap f) (conc_vp_p p)).
Proof.
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** conc_conc2_r_inv2_r_'conc_p_vp'_q です。 *)
(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1013 *)
Definition conc_conc2_r_inv2_r_'conc_p_vp'_q@{i | }
  {A : Type@{i}} {x y : A} (p q : Path@{i} x y) (r : Path@{i} p q)
  : Path@{i} (conc (conc2 r (inv2 r)) (conc_p_vp q)) (conc_p_vp p).
Proof.
  refine (match r with idpath => _ end).
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** conc_conc2_inv2_r_r_'conc_vp_p'_q です。 *)
(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1019 *)
Definition conc_conc2_inv2_r_r_'conc_vp_p'_q@{i | }
  {A : Type@{i}} {x y : A} (p q : Path@{i} x y) (r : Path@{i} p q)
  : Path@{i} (conc (conc2 (inv2 r) r) (conc_vp_p q)) (conc_vp_p p).
Proof.
  refine (match r with idpath => _ end).
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** ** 髭付け (wiskering) *)

(** [Path (conc p q) (p r)] です。 *)
(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1027 *)
Definition path_cpq_cpr@{i | }
  {A : Type@{i}} {x y z : A} (p : Path@{i} x y) {q r : Path@{i} y z}
  : Path@{i} q r -> Path@{i} (conc p q) (conc p r)
  := fun h => conc2 idpath h.

(** [Path (conc p r) (q r)] です。 *)
(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1031 *)
Definition path_cpr_cqr@{i | }
  {A : Type@{i}} {x y z : A} {p q : Path@{i} x y} (r : Path@{i} y z)
  : Path@{i} p q -> Path@{i} (conc p r) (conc q r)
  := fun h => conc2 h idpath.
