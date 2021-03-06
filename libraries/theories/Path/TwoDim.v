(* Run with -nois. *)
(** [GiC.Path.TwoDim] は、ある型とその上の道とその上の道が二次元の亜群の構造として見做せることに関する定理を提供します。

    具体的には、 [(A, Path A x y, Path (Path A x y) p q)] が二次元の亜群になることに由来する定理を定義します。
 *)

(** 必要なライブラリを要求します。 *)

Require GiC.Base.
Require GiC.Path.Base.
Require GiC.Path.OneDim.

(** 必要なモジュールをインポートします。 *)

Import GiC.Base.
Import GiC.Path.Base.
Import GiC.Path.OneDim.

(** 帰納原理 (induction principle) を生成しないように設定します。 *)

Unset Elimination Schemes.

(** 宇宙多相 (universe polymorphism) について設定します。 *)

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

(** タクティックが使用できるように設定します。 *)

Set Default Proof Mode "Classic".

(** ビュレットを使用しないときにエラーになるように設定します。 *)

Set Default Goal Selector "!".

(** ** 高階での一貫性 (coherence) に関する定理 *)

(** [conc2 (ap f p) (ap g p)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L984 *)
Definition conc2_ap_f_p_ap_g_p@{i j | }
  {A : Type@{i}} {B : Type@{j}}
  {x' y' z' : B} (f : A -> Path@{j} x' y') (g : A -> Path@{j} y' z')
  {x y : A} (p : Path@{i} x y)
  : Path@{j} (conc2 (ap f p) (ap g p)) (ap (fun x : A => conc (f x) (g x)) p).
Proof.
  path_elim p.
  cbv.
  exact idpath.
Defined.

(** [conc (ap_f_cpq f p (inv p)) (conc (conc2 idpath (ap_f_vp f p)) (conc_p_vp (ap f p)))] です。 *)

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
  path_elim p.
  cbv.
  exact idpath.
Defined.

(** [conc (ap_f_cpq f (inv p) p) (conc (conc2 (ap_f_vp f p idpath) (conc_vp_p (ap f p))))] です。 *)

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
  path_elim p.
  cbv.
  exact idpath.
Defined.

(** [conc (conc2 r (inv2 r)) (conc_p_vp q)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1013 *)
Definition conc_conc2_r_inv2_r_'conc_p_vp'_q@{i | }
  {A : Type@{i}} {x y : A} (p q : Path@{i} x y) (r : Path@{i} p q)
  : Path@{i} (conc (conc2 r (inv2 r)) (conc_p_vp q)) (conc_p_vp p).
Proof.
  path_elim r.
  path_elim p.
  cbv.
  exact idpath.
Defined.

(** [conc (conc2 (inv2 r) r) (conc_vp_p q)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1019 *)
Definition conc_conc2_inv2_r_r_'conc_vp_p'_q@{i | }
  {A : Type@{i}} {x y : A} (p q : Path@{i} x y) (r : Path@{i} p q)
  : Path@{i} (conc (conc2 (inv2 r) r) (conc_vp_p q)) (conc_vp_p p).
Proof.
  path_elim r.
  path_elim p.
  cbv.
  exact idpath.
Defined.

(** ** 髭付け (whiskering) *)

(** 左からの髭付けです。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1027 *)
Definition whiskerL@{i | }
  {A : Type@{i}} {x y z : A}
  (p : Path@{i} x y) {q r : Path@{i} y z} (h : Path@{i} q r)
  : Path@{i} (conc p q) (conc p r)
  := conc2 idpath h.

(** 右からの髭付けです。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1031 *)
Definition whiskerR@{i | }
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
  refine_by_conc (conc (inv p) (conc p q)).
  -
    exact (inv (conc_vp_cpq p q)).
  -
  refine_by_conc (conc (inv p) (conc p r)).
  +
    refine (whiskerL (inv p) h).
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
  refine_by_conc (conc (conc p r) (inv r)).
  -
    exact (inv (conc_cpq_vq p r)).
  -
  refine_by_conc (conc (conc q r) (inv r)).
  +
    refine (whiskerR h (inv r)).
  +
    exact (conc_cpq_vq q r).
Defined.

(** [conc (conc (inv (conc_p_1 p)) (whiskerR h idpath)) (conc_p_1 q)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1047 *)
Definition conc_conc_inv_'conc_p_1'_p_whiskerR_h_1_'conc_p_1'_q@{i | }
  {A : Type@{i}} {x y : A} {p q : Path@{i} x y} (h : Path@{i} p q)
  : Path@{i}
    (conc (conc (inv (conc_p_1 p)) (whiskerR h idpath)) (conc_p_1 q))
    h.
Proof.
  path_elim h.
  path_elim p.
  cbv.
  exact idpath.
Defined.

(** [whiskerR (idpath p) q] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1055 *)
Definition whiskerR_idpath_p_q@{i | }
  {A : Type@{i}} {x y z : A} (p : Path@{i} x y) (q : Path@{i} y z)
  : Path@{i} (whiskerR (idpath p) q) (idpath (conc p q)).
Proof.
  path_elim q.
  cbv.
  exact idpath.
Defined.

(** [whiskerL p (idpath q)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1060 *)
Definition whiskerL_p_idpath_q@{i | }
  {A : Type@{i}} {x y z : A} (p : Path@{i} x y) (q : Path@{i} y z)
  : Path@{i} (whiskerL p (idpath q)) (idpath (conc p q)).
Proof.
  path_elim p.
  cbv.
  exact idpath.
Defined.

(** [conc (conc (inv (conc_1_p p)) (whiskerL idpath h)) (conc_1_p q)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1065 *)
Definition conc_conc_inv_'conc_1_p'_p_whiskerL_1_h_'conc_1_p'_q@{i | }
  {A : Type@{i}} {x y : A} {p q : Path@{i} x y} (h : Path@{i} p q)
  : Path@{i}
    (conc (conc (inv (conc_1_p p)) (whiskerL idpath h)) (conc_1_p q))
    h.
Proof.
  path_elim h.
  path_elim p.
  cbv.
  exact idpath.
Defined.

(** [whiskerR h (idpath x)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1073 *)
Definition whiskerR_h_idpath_x@{i | }
  {A : Type@{i}} (x : A) (h : Path@{i} (idpath x) (idpath x))
  : Path@{i} (whiskerR h (idpath x)) h.
Proof.
  refine_by_conc
    (conc
      (conc (inv (conc_p_1 idpath)) (whiskerR h idpath))
      (conc_p_1 idpath)).
  -
    change
      (Path@{i}
        (whiskerR h idpath)
        (conc (conc idpath (whiskerR h idpath)) idpath)).
    refine_by_conc (conc idpath (whiskerR h idpath)).
    +
      exact (inv (conc_1_p (whiskerR h idpath))).
    +
      exact (inv (conc_p_1 (conc idpath (whiskerR h idpath)))).
  -
    exact (conc_conc_inv_'conc_p_1'_p_whiskerR_h_1_'conc_p_1'_q h).
Defined.

(** [whiskerL (idpath x) h] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1080 *)
Definition whiskerL_idpath_x_h@{i | }
  {A : Type@{i}} (x : A) (h : Path@{i} (idpath x) (idpath x))
  : Path@{i} (whiskerL (idpath x) h) h.
Proof.
  refine_by_conc
    (conc (conc (inv (conc_1_p idpath)) (whiskerL idpath h)) (conc_1_p idpath)).
  -
    change
      (Path@{i}
        (whiskerL idpath h)
        (conc (conc idpath (whiskerL idpath h)) idpath)).
    refine_by_conc (conc idpath (whiskerL idpath h)).
    +
      exact (inv (conc_1_p (whiskerL idpath h))).
    +
      exact (inv (conc_p_1 (conc idpath (whiskerL idpath h)))).
  -
    exact (conc_conc_inv_'conc_1_p'_p_whiskerL_1_h_'conc_1_p'_q h).
Defined.

(** [conc2 h idpath] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1087 *)
Definition conc2_h_1@{i | }
  {A : Type@{i}} {x y : A} {p q : Path@{i} x y} (h : Path@{i} p q)
  : Path@{i} (conc2 h idpath) (whiskerR h idpath).
Proof.
  unfold whiskerR.
  exact idpath.
Defined.

(** [conc2 idpath h] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1092 *)
Definition conc2_1_h@{i | }
  {A : Type@{i}} {x y : A} {p q : Path@{i} x y} (h : Path@{i} p q)
  : Path@{i} (conc2 idpath h) (whiskerL idpath h).
Proof.
  unfold whiskerL.
  exact idpath.
Defined.

(** [Path (conc2 g h) (conc2 g k) -> Path h k] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1097 *)
Definition fun_Path_conc2_g_h_conc2_g_k_Path_h_k@{i | }
  {A : Type@{i}} {x y z : A} {p p' : Path@{i} x y} {q q' : Path@{i} y z}
  (g : Path@{i} p p') (h k : Path@{i} q q')
  : Path@{i} (conc2 g h) (conc2 g k) -> Path@{i} h k.
Proof.
  path_elim g.
  refine (let t := _ in t q' h k).
  path_elim q.
  path_elim p.
  refine (fun q'_ h_ k_ r_ => _).

  refine_by_conc
    (conc
      (conc (inv (conc_1_p idpath)) (whiskerL idpath h_))
      (conc_1_p q'_)).
  -
    exact
      (inv (conc_conc_inv_'conc_1_p'_p_whiskerL_1_h_'conc_1_p'_q h_)).
  -
  refine_by_conc
    (conc
      (conc (inv (conc_p_1 idpath)) (whiskerR k_ idpath))
      (conc_p_1 q'_)).
  +
    refine (whiskerR _ (conc_1_p q'_)).
    refine (whiskerL (inv (conc_1_p idpath)) _).
    exact r_.
  +
    exact (conc_conc_inv_'conc_p_1'_p_whiskerR_h_1_'conc_p_1'_q k_).
Defined.

(** [Path (conc2 g k) (conc2 h k) -> Path g h] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1107 *)
Definition fun_Path_conc2_g_k_conc2_h_k_Path_g_h@{i | }
  {A : Type@{i}} {x y z : A} {p p' : Path@{i} x y} {q q' : Path@{i} y z}
  (g h : Path@{i} p p') (k : Path@{i} q q')
  : Path@{i} (conc2 g k) (conc2 h k) -> Path@{i} g h.
Proof.
  path_elim k.
  path_elim q.
  refine (let t := _ in t p' g h).
  path_elim p.
  refine (fun p'_ g_ h_ r_ => _).

  refine_by_conc
    (conc
      (conc (inv (conc_p_1 idpath)) (whiskerR g_ idpath))
      (conc_p_1 p'_)).
  -
    exact (inv (conc_conc_inv_'conc_p_1'_p_whiskerR_h_1_'conc_p_1'_q g_)).
  -
  refine_by_conc
    (conc
      (conc (inv (conc_1_p idpath)) (whiskerL idpath h_))
      (conc_1_p p'_)).
  +
    refine (whiskerR _ (conc_p_1 p'_)).
    refine (whiskerL (inv (conc_p_1 idpath)) _).
    exact r_.
  +
    exact (conc_conc_inv_'conc_1_p'_p_whiskerL_1_h_'conc_1_p'_q h_).
Defined.

(** ** 髭付けと道の結合 *)

(** [whiskerL p (conc r s)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1121 *)
Definition whiskerL_p_conc_r_s@{i | }
  {A : Type@{i}} {x y z : A} (p : Path@{i} x y) {q q' q'' : Path@{i} y z}
  (r : Path@{i} q q') (s : Path@{i} q' q'')
  : Path@{i} (whiskerL p (conc r s)) (conc (whiskerL p r) (whiskerL p s)).
Proof.
  path_elim s.
  path_elim r.
  path_elim q.
  path_elim p.
  cbv.
  exact idpath.
Defined.

(** [whiskerR (conc r s) q] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1128 *)
Definition whiskerR_conc_r_s_q@{i | }
  {A : Type@{i}} {x y z : A} {p p' p'' : Path@{i} x y} (q : Path@{i} y z)
  (r : Path@{i} p p') (s : Path@{i} p' p'')
  : Path@{i} (whiskerR (conc r s) q) (conc (whiskerR r q) (whiskerR s q)).
Proof.
  path_elim s.
  path_elim r.
  path_elim p.
  path_elim q.
  cbv.
  exact idpath.
Defined.

(** [conc (conc (inv (conc_vp_cpq p q)) (whiskerL (inv p) (whiskerL p r))) (conc_vp_cpq p q')] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1136 *)
Definition conc_conc_inv_'conc_vp_cpq'_p_q_whiskerL_inv_p_whiskerL_p_r_'conc_vp_cpq'_p_q'
  @{i | }
  {A : Type@{i}} {x y z : A} (p : Path@{i} x y)
  {q q' : Path@{i} y z} (r : Path@{i} q q')
  : Path@{i}
    (conc
      (conc (inv (conc_vp_cpq p q)) (whiskerL (inv p) (whiskerL p r)))
      (conc_vp_cpq p q'))
    r.
Proof.
  path_elim r.
  path_elim q.
  path_elim p.
  cbv.
  exact idpath.
Defined.

(** [conc (conc (inv (conc_p_cvpq p q)) (whiskerL p (whiskerL (inv p) r))) (conc_p_cvpq p q')] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1144 *)
Definition conc_conc_inv_'conc_p_cvpq'_p_q_whiskerL_p_whiskerL_inv_p_r_'conc_p_cvpq'_p_q'
  @{i | }
  {A : Type@{i}} {x y z : A} (p : Path@{i} y x)
  {q q' : Path@{i} y z} (r : Path@{i} q q')
  : Path@{i}
    (conc
      (conc (inv (conc_p_cvpq p q)) (whiskerL p (whiskerL (inv p) r)))
      (conc_p_cvpq p q'))
    r.
Proof.
  path_elim r.
  path_elim q.
  path_elim p.
  cbv.
  exact idpath.
Defined.

(** [conc (conc (inv (conc_cpq_vq p q)) (whiskerR (whiskerR r q) (inv q))) (conc_cpq_vq p' q)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1152 *)
Definition conc_conc_inv_'conc_cpq_vp'_p_q_whiskerR_whiskerR_r_q_inv_q_'conc_cpq_vq'_p'_q
  @{i | }
  {A : Type@{i}} {x y z : A} {p p' : Path@{i} x y}
  (r : Path@{i} p p') (q : Path@{i} y z)
  : Path@{i}
    (conc
      (conc (inv (conc_cpq_vq p q)) (whiskerR (whiskerR r q) (inv q)))
      (conc_cpq_vq p' q))
    r.
Proof.
  path_elim r.
  path_elim q.
  path_elim p.
  cbv.
  exact idpath.
Defined.

(** [conc (conc (inv (conc_cpvq_q p q)) (whiskerR (whiskerR r (inv q)) q)) (conc_cpvq_q p' q)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1160 *)
Definition conc_conc_inv_'conc_cpvq_q'_p_q_whiskerR_whiskerR_r_inv_q_q_'conc_cpvq_q'_p'_q
  @{i | }
  {A : Type@{i}} {x y z : A} {p p' : Path@{i} x y}
  (r : Path@{i} p p') (q : Path@{i} z y)
  : Path@{i}
    (conc
      (conc (inv (conc_cpvq_q p q)) (whiskerR (whiskerR r (inv q)) q))
      (conc_cpvq_q p' q))
    r.
Proof.
  path_elim r.
  refine (let t := _ in t p).
  path_elim q.
  refine (fun p_ => _).
  path_elim p_.
  cbv.
  exact idpath.
Defined.

(** ** 交支法則 (interchange law) *)

(** [conc (conc2 a c) (conc2 b d)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1169 *)
Definition conc_conc2_a_c_conc2_b_d@{i | }
  {A : Type@{i}} {x y z : A}
  {p p' p'' : Path@{i} x y} {q q' q'' : Path@{i} y z}
  (a : Path@{i} p p') (b : Path@{i} p' p'')
  (c : Path@{i} q q') (d : Path@{i} q' q'')
  : Path@{i} (conc (conc2 a c) (conc2 b d)) (conc2 (conc a b) (conc c d)).
Proof.
  path_elim d.
  path_elim c.
  path_elim b.
  path_elim a.
  cbv.
  exact idpath.
Defined.

(** [conc (whiskerR a q) (whiskerL p' b)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1169 *)
Definition conc_whiskerR_a_q_whiskerL_p'_b@{i | }
  {A : Type@{i}} {x y z : A}
  {p p' : Path@{i} x y} {q q' : Path@{i} y z}
  (a : Path@{i} p p') (b : Path@{i} q q')
  : Path@{i}
    (conc (whiskerR a q) (whiskerL p' b))
    (conc (whiskerL p b) (whiskerR a q')).
Proof.
  path_elim b.
  path_elim a.
  cbv.
  exact idpath.
Defined.

(** ** 2-圏における一貫性 (coherence) に関する定理 *)

(** [(A, Path A _ _, Path (Path A _ _) _ _)] による 2-圏における五角形恒等式 (pentagon identity) です。これは identity ではなく 3-圏以上の構造による isomorphism であるため、正確には pentagonator です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1194 *)
Definition pentagonatorPathPath@{i | }
  {A : Type@{i}} {v w x y z : A}
  (p : Path@{i} v w) (q : Path@{i} w x) (r : Path@{i} x y) (s : Path@{i} y z)
  : Path@{i}
    (conc
      (conc
        (whiskerL p (conc_p_cqr q r s))
        (conc_p_cqr p (conc q r) s))
      (whiskerR (conc_p_cqr p q r) s))
    (conc
      (conc_p_cqr p q (conc r s))
      (conc_p_cqr (conc p q) r s)).
Proof.
  path_elim s.
  path_elim r.
  path_elim q.
  path_elim p.
  cbv.
  exact idpath.
Defined.

(** [(A, Path A _ _, Path (Path A _ _) _ _)] による 2-圏における三角形恒等式 (triangle identity) です。これは identity ではなく 3-圏以上の構造による isomorphism であるため、正確には triangulator です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1204 *)
Definition triangulatorPathPath@{i | }
  {A : Type@{i}} {x y z : A} (p : Path@{i} x y) (q : Path@{i} y z)
  : Path@{i}
    (conc (conc_p_cqr p idpath q) (whiskerR (conc_p_1 p) q))
    (whiskerL p (conc_1_p q)).
Proof.
  path_elim q.
  path_elim p.
  cbv.
  exact idpath.
Defined.

(** the Eckmann–Hilton argument による交換法則の証明です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1212 *)
Definition theEckmannHiltonArgumentPathPath@{i | }
  {A : Type@{i}} {x : A} (p q : Path@{i} (idpath x) (idpath x))
  : Path@{i} (conc p q) (conc q p).
Proof.
  refine_by_conc
    (conc
      (conc
        (conc
          (inv (conc_p_1 idpath))
          (whiskerR p idpath))
        (conc_p_1 idpath))
      (conc
        (conc
          (inv (conc_1_p idpath))
          (whiskerL idpath q))
        (conc_1_p idpath))).
  -
    refine (inv _).
    refine (conc2 _ _).
    +
      exact (conc_conc_inv_'conc_p_1'_p_whiskerR_h_1_'conc_p_1'_q p).
    +
      exact (conc_conc_inv_'conc_1_p'_p_whiskerL_1_h_'conc_1_p'_q q).
  -
  refine_by_conc
    (conc
      (conc
        (inv (conc_p_1 idpath))
        (whiskerR p idpath))
      (conc
        (inv (conc_1_p idpath))
        (whiskerL idpath q))).
  +
    refine (conc2 _ _).
    *
      exact (conc_p_1 (conc (inv (conc_p_1 idpath)) (whiskerR p idpath))).
    *
      exact (conc_1_p (conc (inv (conc_1_p idpath)) (whiskerL idpath q))).
  +
  refine_by_conc
    (conc
      (whiskerR p idpath)
      (whiskerL idpath q)).
  *
    refine (conc2 _ _).
    --
      exact (conc_1_p (whiskerR p idpath)).
    --
      exact (conc_1_p (whiskerL idpath q)).
  *
  refine_by_conc
    (conc
      (whiskerL idpath q)
      (whiskerR p idpath)).
  --
    exact (conc_whiskerR_a_q_whiskerL_p'_b p q).
  --
  refine_by_conc
    (conc
      (conc
        (inv (conc_1_p idpath))
        (whiskerL idpath q))
      (conc
        (inv (conc_1_p idpath))
        (whiskerR p idpath))).
  ++
    refine (inv _).
    refine (conc2 _ _).
    **
      exact (conc_1_p (whiskerL idpath q)).
    **
      exact (conc_1_p (whiskerR p idpath)).
  ++
  refine_by_conc
    (conc
      (conc
        (conc
          (inv (conc_1_p idpath))
          (whiskerL idpath q))
        (conc_1_p idpath))
      (conc
        (conc
          (inv (conc_1_p idpath))
          (whiskerR p idpath))
        (conc_p_1 idpath))).
  **
    refine (inv _).
    refine (conc2 _ _).
    ---
      exact (conc_p_1 (conc (inv (conc_1_p idpath)) (whiskerL idpath q))).
    ---
      exact (conc_p_1 (conc (inv (conc_1_p idpath)) (whiskerR p idpath))).
  **
    refine (conc2 _ _).
    ---
      exact (conc_conc_inv_'conc_1_p'_p_whiskerL_1_h_'conc_1_p'_q q).
    ---
      exact (conc_conc_inv_'conc_p_1'_p_whiskerR_h_1_'conc_p_1'_q p).
Defined.
