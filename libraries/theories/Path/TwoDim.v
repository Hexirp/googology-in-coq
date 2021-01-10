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
  refine (match p with idpath => _ end).
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
  refine (match p with idpath => _ end).
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
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** [conc (conc2 r (inv2 r)) (conc_p_vp q)] です。 *)

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

(** [conc (conc2 (inv2 r) r) (conc_vp_p q)] です。 *)

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
  refine_conc (conc (inv p) (conc p q)).
  -
    exact (inv (conc_vp_cpq p q)).
  -
  refine_conc (conc (inv p) (conc p r)).
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
  refine_conc (conc (conc p r) (inv r)).
  -
    exact (inv (conc_cpq_vq p r)).
  -
  refine_conc (conc (conc q r) (inv r)).
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
  refine (match h with idpath => _ end).
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** [whiskerR (idpath p) q] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1055 *)
Definition whiskerR_idpath_p_q@{i | }
  {A : Type@{i}} {x y z : A} (p : Path@{i} x y) (q : Path@{i} y z)
  : Path@{i} (whiskerR (idpath p) q) (idpath (conc p q)).
Proof.
  refine (match q with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** [whiskerL p (idpath q)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1060 *)
Definition whiskerL_p_idpath_q@{i | }
  {A : Type@{i}} {x y z : A} (p : Path@{i} x y) (q : Path@{i} y z)
  : Path@{i} (whiskerL p (idpath q)) (idpath (conc p q)).
Proof.
  refine (match p with idpath => _ end).
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
  refine (match h with idpath => _ end).
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** [whiskerR h (idpath x)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1073 *)
Definition whiskerR_h_idpath_x@{i | }
  {A : Type@{i}} (x : A) (h : Path@{i} (idpath x) (idpath x))
  : Path@{i} (whiskerR h (idpath x)) h.
Proof.
  refine_conc
    (conc
      (conc (inv (conc_p_1 idpath)) (whiskerR h idpath))
      (conc_p_1 idpath)).
  -
    change
      (Path@{i}
        (whiskerR h idpath)
        (conc (conc idpath (whiskerR h idpath)) idpath)).
    refine_conc (conc idpath (whiskerR h idpath)).
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
  refine_conc
    (conc (conc (inv (conc_1_p idpath)) (whiskerL idpath h)) (conc_1_p idpath)).
  -
    change
      (Path@{i}
        (whiskerL idpath h)
        (conc (conc idpath (whiskerL idpath h)) idpath)).
    refine_conc (conc idpath (whiskerL idpath h)).
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
  refine
    (match g
      as g_
      in Path _ p'_
      return Path@{i} (conc2 g_ h) (conc2 g_ k) -> Path@{i} h k
      with idpath => _
    end).
  refine (let t := _ in t q q' h k).
  refine
    (match p
      as p_
      in Path _ y_
      return
        forall
          (q_ q'_ : Path@{i} y_ z)
          (h_ k_ : @Path@{i} (Path@{i} y_ z) q_ q'_),
          forall _
            : @Path@{i}
              (Path@{i} (@conc1 A x y_ z p_ q_) (@conc1 A x y_ z p_ q'_))
              (@conc2 A x y_ z p_ p_ q_ q'_ (@idpath (Path@{i} x y_) p_) h_)
              (@conc2 A x y_ z p_ p_ q_ q'_ (@idpath (Path@{i} x y_) p_) k_),
            @Path@{i} (@Path@{i} (Path@{i} y_ z) q_ q'_) h_ k_
      with idpath => _
    end).
  refine (fun q_ => _).
  refine
    (match q_
      as q__
      in Path _ z_
      return
        forall
          (q'__ : Path@{i} x z_)
          (h__ k__ : @Path@{i} (Path@{i} x z_) q__ q'__),
          forall _
            : @Path@{i}
              (@Path@{i}
                (Path@{i} x z_)
                (@conc1 A x x z_ idpath q__)
                (@conc1 A x x z_ idpath q'__))
              (@conc2 A x x z_ idpath idpath q__ q'__ idpath h__)
              (@conc2 A x x z_ idpath idpath q__ q'__ idpath k__),
            @Path@{i} (@Path@{i} (Path@{i} x z_) q__ q'__) h__ k__
      with idpath => _
    end).
  refine (fun q'__ h__ k__ r__ => _).

  refine_conc
    (conc
      (conc (inv (conc_1_p idpath)) (whiskerL idpath h__))
      (conc_1_p q'__)).
  -
    exact
      (inv (conc_conc_inv_'conc_1_p'_p_whiskerL_1_h_'conc_1_p'_q h__)).
  -
  refine_conc
    (conc
      (conc (inv (conc_p_1 idpath)) (whiskerR k__ idpath))
      (conc_p_1 q'__)).
  +
    refine (whiskerR _ (conc_1_p q'__)).
    refine (whiskerL (inv (conc_1_p idpath)) _).
    exact r__.
  +
    exact (conc_conc_inv_'conc_p_1'_p_whiskerR_h_1_'conc_p_1'_q k__).
Defined.

(** [Path (conc2 g k) (conc2 h k) -> Path g h] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1107 *)
Definition fun_Path_conc2_g_k_conc2_h_k_Path_g_h@{i | }
  {A : Type@{i}} {x y z : A} {p p' : Path@{i} x y} {q q' : Path@{i} y z}
  (g h : Path@{i} p p') (k : Path@{i} q q')
  : Path@{i} (conc2 g k) (conc2 h k) -> Path@{i} g h.
Proof.
  refine
    (match k
      as k_
      in Path _ q'_
      return Path@{i} (conc2 g k_) (conc2 h k_) -> Path@{i} g h
      with idpath => _
    end).
  refine (let t := _ in t p' q g h).
  refine
    (match p
      as p_
      in Path _ y_
      return
        forall
          (p'_ : Path@{i} x y_) (q_ : Path@{i} y_ z)
          (g_ h_ : Path@{i} p_ p'_),
        Path@{i} (conc2 g_ idpath) (conc2 h_ idpath) -> Path@{i} g_ h_
      with idpath => _
    end).
  refine (fun p'_ q_ => _ p'_).
  refine
    (match q_
      as q_
      in Path _ z_
      return
        forall (p'__ : Path@{i} x x) (g__ h__ : Path@{i} idpath p'__),
          Path@{i} (conc2 g__ idpath) (conc2 h__ idpath) -> Path@{i} g__ h__
      with idpath => _
    end).
  refine (fun p'__ g__ h__ r__ => _).

  refine_conc
    (conc
      (conc (inv (conc_p_1 idpath)) (whiskerR g__ idpath))
      (conc_p_1 p'__)).
  -
    exact (inv (conc_conc_inv_'conc_p_1'_p_whiskerR_h_1_'conc_p_1'_q g__)).
  -
  refine_conc
    (conc
      (conc (inv (conc_1_p idpath)) (whiskerL idpath h__))
      (conc_1_p p'__)).
  +
    refine (whiskerR _ (conc_p_1 p'__)).
    refine (whiskerL (inv (conc_p_1 idpath)) _).
    exact r__.
  +
    exact (conc_conc_inv_'conc_1_p'_p_whiskerL_1_h_'conc_1_p'_q h__).
Defined.

(** ** 髭付けと道の結合 *)

(** [wiskerL p (conc r s)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1121 *)
Definition whiskerL_p_conc_r_s@{i | }
  {A : Type@{i}} {x y z : A} (p : Path@{i} x y) {q q' q'' : Path@{i} y z}
  (r : Path@{i} q q') (s : Path@{i} q' q'')
  : Path@{i} (whiskerL p (conc r s)) (conc (whiskerL p r) (whiskerL p s)).
Proof.
  refine (match s with idpath => _ end).
  refine (match r with idpath => _ end).
  refine (match q with idpath => _ end).
  refine (match p with idpath => _ end).
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
  refine (match s with idpath => _ end).
  refine (match r with idpath => _ end).
  refine (match p with idpath => _ end).
  refine (match q with idpath => _ end).
  cbv.
  exact idpath.
Defined.
