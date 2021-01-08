(* Run with -nois. *)
(** [GiC.Path.TwoDim] は、ある型とその上の道とその上の道が二次元の亜群の構造として見做せることに関する定理を提供します。

    具体的には、 [(A, Path A x y, Path (Path A x y) p q)] が二次元の亜群になることに由来する定理を定義します。
 *)

(** 必要なライブラリを要求します。 *)

Require GiC.Base.
Require GiC.Path.Base.
Require GiC.Path.OneDim.

(** 必要なライブラリをインポートします。 *)

Import GiC.Base.
Import GiC.Path.Base.
Import GiC.Path.OneDim.

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

(** 左からの髭付けです。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1027 *)
Definition wiskerL@{i | }
  {A : Type@{i}} {x y z : A}
  (p : Path@{i} x y) {q r : Path@{i} y z} (h : Path@{i} q r)
  : Path@{i} (conc p q) (conc p r)
  := conc2 idpath h.

(** 右からの髭付けです。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1031 *)
Definition wiskerR@{i | }
  {A : Type@{i}} {x y z : A}
  {p q : Path@{i} x y} (h : Path@{i} p q) (r : Path@{i} y z)
  : Path@{i} (conc p r) (conc q r)
  := conc2 h idpath.

(** [Path (conc p q) (conc p r) -> Path q r] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1037 *)
Definition fun_Path_cpq_cpr_Path_q_r@{i | }
  {A : Type@{i}} {x y z : A} (p : Path@{i} x y) (q r : Path@{i} y z)
  : Path@{i} (conc p q) (conc p r) -> Path@{i} q r.
Proof.
  refine (fun h => _).
  refine_conc (conc (inv p) (conc p q)).
  -
    exact (inv (conc_vp_cpq p q)).
  -
  refine_conc (conc (inv p) (conc p r)).
  +
    refine (wiskerL (inv p) h).
  +
    exact (conc_vp_cpq p r).
Defined.

(** [Path (conc p r) (conc q r) -> Path p q] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1041 *)
Definition fun_Path_cpr_cqr_Path_p_q@{i | }
  {A : Type@{i}} {x y z : A} (p q : Path@{i} x y) (r : Path@{i} y z)
  : Path@{i} (conc p r) (conc q r) -> Path@{i} p q.
Proof.
  refine (fun h => _).
  refine_conc (conc (conc p r) (inv r)).
  -
    exact (inv (conc_cpq_vq p r)).
  -
  refine_conc (conc (conc q r) (inv r)).
  +
    refine (wiskerR h (inv r)).
  +
    exact (conc_cpq_vq q r).
Defined.

(** [conc (conc (inv (conc_p_1 p)) (wiskerR h idpath)) (conc_p_1 q)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1047 *)
Definition conc_conc_inv_'conc_p_1'_p_wiskerR_h_1_'conc_p_1'_q@{i | }
  {A : Type@{i}} {x y : A} {p q : Path@{i} x y} (h : Path@{i} p q)
  : Path@{i}
    (conc (conc (inv (conc_p_1 p)) (wiskerR h idpath)) (conc_p_1 q))
    h.
Proof.
  refine (match h with idpath => _ end).
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** [wiskerR (idpath p) q] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1055 *)
Definition wiskerR_idpath_p_q@{i | }
  {A : Type@{i}} {x y z : A} (p : Path@{i} x y) (q : Path@{i} y z)
  : Path@{i} (wiskerR (idpath p) q) (idpath (conc p q)).
Proof.
  refine (match q with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** [wiskerL p (idpath q)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1060 *)
Definition wiskerL_p_idpath_q@{i | }
  {A : Type@{i}} {x y z : A} (p : Path@{i} x y) (q : Path@{i} y z)
  : Path@{i} (wiskerL p (idpath q)) (idpath (conc p q)).
Proof.
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** [conc (conc (inv (conc_1_p p)) (wiskerL idpath h)) (conc_1_p q)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1065 *)
Definition conc_conc_inv_'conc_1_p'_p_wiskerL_1_h_'conc_1_p'_q@{i | }
  {A : Type@{i}} {x y : A} {p q : Path@{i} x y} (h : Path@{i} p q)
  : Path@{i}
    (conc (conc (inv (conc_1_p p)) (wiskerL idpath h)) (conc_1_p q))
    h.
Proof.
  refine (match h with idpath => _ end).
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** [wiskerR h (idpath x)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1073 *)
Definition wiskerR_h_idpath_x@{i | }
  {A : Type@{i}} (x : A) (h : Path@{i} (idpath x) (idpath x))
  : Path@{i} (wiskerR h (idpath x)) h.
Proof.
  refine_conc (conc (conc (inv (conc_p_1 idpath)) (wiskerR h idpath)) (conc_p_1 idpath)).
  -
    change (Path@{i} (wiskerR h idpath) (conc (conc idpath (wiskerR h idpath)) idpath)).
    refine_conc (conc idpath (wiskerR h idpath)).
    +
      exact (inv (conc_1_p (wiskerR h idpath))).
    +
      exact (inv (conc_p_1 (conc idpath (wiskerR h idpath)))).
  -
    exact (conc_conc_inv_'conc_p_1'_p_wiskerR_h_1_'conc_p_1'_q h).
Defined.

(** [wiskerL (idpath x) h] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1080 *)
Definition wiskerL_idpath_x_h@{i | }
  {A : Type@{i}} (x : A) (h : Path@{i} (idpath x) (idpath x))
  : Path@{i} (wiskerL (idpath x) h) h.
Proof.
  refine_conc (conc (conc (inv (conc_1_p idpath)) (wiskerL idpath h)) (conc_1_p idpath)).
  -
    change (Path@{i} (wiskerL idpath h) (conc (conc idpath (wiskerL idpath h)) idpath)).
    refine_conc (conc idpath (wiskerL idpath h)).
    +
      exact (inv (conc_1_p (wiskerL idpath h))).
    +
      exact (inv (conc_p_1 (conc idpath (wiskerL idpath h)))).
  -
    exact (conc_conc_inv_'conc_1_p'_p_wiskerL_1_h_'conc_1_p'_q h).
Defined.
