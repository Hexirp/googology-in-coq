(* Run with -nois. *)

(** * GiC.Path.Transposition *)

(** [GiC.Path.Transposition] は、一次元の亜群の構造における等式について、その移項を行う補題を提供します。

    具体的には、たとえば [p ∘ q = r] から [p = r ∘ q⁻¹] を導くという風な補題を組み合わせ的に網羅しています。
 *)

(** 必要なライブラリをインポートします。 *)
Require Import GiC.Base GiC.Path.Base GiC.Path.OneDim.

(** 帰納原理 (induction principle) を生成しないように設定します。 *)
Unset Elimination Schemes.

(** 宇宙多相 (universe polymorphism) について設定します。 *)
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

(** 宇宙 (universe) について表示するように設定します。 *)
Set Printing Universes.

(** タクティックが使用できるように設定します。 *)
Set Default Proof Mode "Classic".

(** ** 移項のための補題 *)

(** Path_conc_r_p_q です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L176 *)
Definition path_crp_q_L@{i | } {A : Type@{i}} {x y z : A}
  : forall (p : Path@{i} x z) (q : Path@{i} y z) (r : Path@{i} y x),
    Path@{i} p (conc (inv r) q) -> Path@{i} (conc r p) q.
Proof.
  move=> p q r.
  refine (let t := _ in t p).
  refine (match r
    as r'
    in Path _ x'
    return forall p' : Path@{i} x' z,
      Path@{i} p' (conc (inv r') q) -> Path@{i} (conc r' p') q
    with idpath => _
  end).

  move=> p' path_p'_cv1q.
  refine_conc p'.
  -
    exact (conc_1_p p').
  -
  refine_conc (conc (inv idpath) q).
  +
    exact path_p'_cv1q.
  +
  simpl inv.
  exact (conc_1_p q).
Defined.

(** Path_conc_r_p_q です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L183 *)
Definition path_crp_q_R@{i | } {A : Type@{i}} {x y z : A}
  : forall (p : Path@{i} x z) (q : Path@{i} y z) (r : Path@{i} y x),
    Path@{i} r (conc q (inv p)) -> Path@{i} (conc r p) q.
Proof.
  move=> p q r.
  refine (let t := _ in t q).
  refine (match p
    as p'
    in Path _ z'
    return forall q' : Path@{i} y z',
      Path@{i} r (conc q' (inv p')) -> Path@{i} (conc r p') q'
    with idpath => _
  end).

  move=> q' path_r_cq'v1.
  refine_conc r.
  -
    exact (conc_p_1 r).
  -
  refine_conc (conc q' (inv idpath)).
  +
    exact path_r_cq'v1.
  +
  simpl inv.
  exact (conc_p_1 q').
Defined.

(** Path_conc_inv_r_p_q です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L190 *)
Definition path_cvrp_q@{i | } {A : Type@{i}} {x y z : A}
  : forall (p : Path@{i} x z) (q : Path@{i} y z) (r : Path@{i} x y),
    Path@{i} p (conc r q) -> Path@{i} (conc (inv r) p) q.
Proof.
  move=> p q r.
  refine (let t := _ in t q).
  refine (match r
    as r'
    in Path _ y'
    return forall q' : Path@{i} y' z,
      Path@{i} p (conc r' q') -> Path@{i} (conc (inv r') p) q'
    with idpath => _
  end).

  move=> q' path_p_c1q'.
  refine_conc p.
  -
    simpl inv.
    exact (conc_1_p p).
  -
  refine_conc (conc idpath q').
  +
    exact path_p_c1q'.
  +
  exact (conc_1_p q').
Defined.

(** Path_conc_r_inv_p_q です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L197 *)
Definition path_crvp_q@{i | } {A : Type@{i}} {x y z : A}
  : forall (p : Path@{i} z x) (q : Path@{i} y z) (r : Path@{i} y x),
    Path@{i} r (conc q p) -> Path@{i} (conc r (inv p)) q.
Proof.
  move=> p q r.
  refine (let t := _ in t r).
  refine (match p
    as p'
    in Path _ x'
    return forall r' : Path@{i} y x',
      Path@{i} r' (conc q p') -> Path@{i} (conc r' (inv p')) q
    with idpath => _
  end).

  move=> r' path_r'_cq1.
  refine_conc r'.
  -
    simpl inv.
    exact (conc_p_1 r').
  -
  refine_conc (conc q idpath).
  +
    exact path_r'_cq1.
  +
  exact (conc_p_1 q).
Defined.

(** Path_q_conc_r_p です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L204 *)
Definition path_q_crp_L@{i | } {A : Type@{i}} {x y z : A}
  : forall (p : Path@{i} x z) (q : Path@{i} y z) (r : Path@{i} y x),
    Path@{i} (conc (inv r) q) p -> Path@{i} q (conc r p).
Proof.
  move=> p q r.
  refine (let t := _ in t p).
  refine (match r
    as r'
    in Path _ x'
    return forall p' : Path@{i} x' z,
      Path@{i} (conc (inv r') q) p' -> Path@{i} q (conc r' p')
    with idpath => _
  end).

  move=> p' path_cv1q_p'.
  refine_conc (conc (inv idpath) q).
  -
    simpl inv.
    exact (inv (conc_1_p q)).
  -
  refine_conc p'.
  +
    exact path_cv1q_p'.
  +
  exact (inv (conc_1_p p')).
Defined.

(** Path_q_conc_r_p です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L211 *)
Definition path_q_crp_R@{i | } {A : Type@{i}} {x y z : A}
  : forall (p : Path@{i} x z) (q : Path@{i} y z) (r : Path@{i} y x),
    Path@{i} (conc q (inv p)) r -> Path@{i} q (conc r p).
Proof.
  move=> p q r.
  refine (let t := _ in t q).
  refine (match p
    as p'
    in Path _ z'
    return forall q' : Path@{i} y z',
      Path@{i} (conc q' (inv p')) r -> Path@{i} q' (conc r p')
    with idpath => _
  end).

  move=> q' path_cq'v1_r.
  refine_conc (conc q' (inv idpath)).
  -
    simpl inv.
    exact (inv (conc_1_p q')).
  -
  refine_conc r.
  +
    exact path_cq'v1_r.
  +
  exact (inv (conc_p_1 r)).
Defined.

(** Path_q_conc_inv_r_p です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L218 *)
Definition path_q_cvrp@{i | } {A : Type@{i}} {x y z : A}
  : forall (p : Path@{i} x z) (q : Path@{i} y z) (r : Path@{i} x y),
    Path@{i} (conc r q) p -> Path@{i} q (conc (inv r) p).
Proof.
  move=> p q r.
  refine (let t := _ in t q).
  refine (match r
    as r'
    in Path _ y'
    return forall q' : Path@{i} y' z,
      Path@{i} (conc r' q') p -> Path@{i} q' (conc (inv r') p)
    with idpath => _
  end).

  move=> q' path_c1q'_p.
  refine_conc (conc idpath q').
  -
    exact (inv (conc_1_p q')).
  -
  refine_conc p.
  +
    exact path_c1q'_p.
  +
  simpl inv.
  exact (inv (conc_p_1 p)).
Defined.

(** Path_q_conc_r_inv_p です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L225 *)
Definition path_q_crvp@{i | } {A : Type@{i}} {x y z : A}
  : forall (p : Path@{i} z x) (q : Path@{i} y z) (r : Path@{i} y x),
    Path@{i} (conc q p) r -> Path@{i} q (conc r (inv p)).
Proof.
  move=> p q r.
  refine (let t := _ in t r).
  refine (match p
    as p'
    in Path _ x'
    return forall r' : Path@{i} y x',
      Path@{i} (conc q p') r' -> Path@{i} q (conc r' (inv p'))
    with idpath => _
  end).

  move=> r' path_cq1_r'.
  refine_conc (conc q idpath).
  -
    exact (inv (conc_p_1 q)).
  -
  refine_conc r'.
  +
    exact path_cq1_r'.
  +
  simpl inv.
  exact (inv (conc_p_1 r')).
Defined.

(** Path_p_q です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L232 *)
Definition path_p_q_L_L@{i | } {A : Type@{i}} {x y : A}
  : forall (p : Path@{i} x y) (q : Path@{i} x y),
    Path@{i} (conc p (inv q)) idpath -> Path@{i} p q.
Proof.
  move=> p q.
  refine (let t := _ in t p).
  refine (match q
    as q'
    in Path _ y'
    return forall p' : Path@{i} x y',
      Path (conc p' (inv q')) idpath -> Path p' q'
    with idpath => _
  end).

  move=> p' path_cp'v1_1.
  refine_conc (conc p' (inv idpath)).
  -
    simpl inv.
    exact (inv (conc_p_1 p')).
  -
  exact path_cp'v1_1.
Defined.

(** Path_p_q です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L239 *)
Definition path_p_q_L_R@{i | } {A : Type@{i}} {x y : A}
  : forall (p : Path@{i} x y) (q : Path@{i} x y),
    Path@{i} (conc (inv q) p) idpath -> Path@{i} p q.
Proof.
  move=> p q.
  refine (let t := _ in t p).
  refine (match q
    as q'
    in Path _ y'
    return forall p' : Path@{i} x y',
      Path (conc (inv q') p') idpath -> Path p' q'
    with idpath => _
  end).

  move=> p' path_cv1p'_1.
  refine_conc (conc (inv idpath) p').
  -
    simpl inv.
    exact (inv (conc_1_p p')).
  -
  exact path_cv1p'_1.
Defined.

(** Path_p_inv_q です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L246 *)
Definition path_p_vq_L@{i | } {A : Type@{i}} {x y : A}
  : forall (p : Path@{i} x y) (q : Path@{i} y x),
    Path@{i} (conc p q) idpath -> Path@{i} p (inv q).
Proof.
  move=> p q.
  refine (let t := _ in t p).
  refine (match q
    as q'
    in Path _ x'
    return forall p' : Path@{i} x' y,
      Path (conc p' q') idpath -> Path p' (inv q')
    with idpath => _
  end).

  move=> p' path_cp'1_1.
  refine_conc (conc p' idpath).
  -
    exact (inv (conc_p_1 p')).
  -
  simpl inv.
  exact path_cp'1_1.
Defined.

(** Path_p_inv_q です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L253 *)
Definition path_p_vq_R@{i | } {A : Type@{i}} {x y : A}
  : forall (p : Path@{i} x y) (q : Path@{i} y x),
    Path@{i} (conc q p) idpath -> Path@{i} p (inv q).
Proof.
  move=> p q.
  refine (let t := _ in t p).
  refine (match q
    as q'
    in Path _ x'
    return forall p' : Path@{i} x' y,
      Path (conc q' p') idpath -> Path p' (inv q')
    with idpath => _
  end).

  move=> p' path_c1p'_1.
  refine_conc (conc idpath p').
  -
    exact (inv (conc_1_p p')).
  -
  simpl inv.
  exact path_c1p'_1.
Defined.

(** Path_p_q です。 *)
(* https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L260 *)
Definition path_p_q_R_L@{i | } {A : Type@{i}} {x y : A}
  : forall (p : Path@{i} x y) (q : Path@{i} x y),
    Path@{i} idpath (conc (inv p) q) -> Path@{i} p q.
Proof.
  move=> p q.
  refine (let t := _ in t q).
  refine (match p
    as p'
    in Path _ y'
    return forall q' : Path@{i} x y',
      Path idpath (conc (inv p') q') -> Path p' q'
    with idpath => _
  end).

  move=> q' path_1_cv1q'.
  refine_conc (conc (inv idpath) q').
  -
    exact path_1_cv1q'.
  -
  simpl inv.
  exact (conc_1_p q').
Defined.

(** Path_p_q です。 *)
(* https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L267 *)
Definition path_p_q_R_R@{i | } {A : Type@{i}} {x y : A}
  : forall (p : Path@{i} x y) (q : Path@{i} x y),
    Path@{i} idpath (conc q (inv p)) -> Path@{i} p q.
Proof.
  move=> p q.
  refine (let t := _ in t q).
  refine (match p
    as p'
    in Path _ y'
    return forall q' : Path@{i} x y',
      Path idpath (conc q' (inv p')) -> Path p' q'
    with idpath => _
  end).

  move=> q' path_1_cq'v1.
  refine_conc (conc q' (inv idpath)).
  -
    exact path_1_cq'v1.
  -
  simpl inv.
  exact (conc_p_1 q').
Defined.

(** Path_inv_p_q です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L274 *)
Definition path_vp_q_L@{i | } {A : Type@{i}} {x y : A}
  : forall (p : Path@{i} x y) (q : Path@{i} y x),
    Path@{i} idpath (conc q p) -> Path@{i} (inv p) q.
Proof.
  move=> p q.
  refine (let t := _ in t q).
  refine (match p
    as p'
    in Path _ y'
    return forall q' : Path@{i} y' x,
      Path idpath (conc q' p') -> Path (inv p') q'
    with idpath => _
  end).

  move=> q' path_1_cq'1.
  refine_conc (conc q' idpath).
  -
    simpl inv.
    exact path_1_cq'1.
  -
  exact (conc_p_1 q').
Defined.

(** Path_inv_p_q です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L281 *)
Definition path_vp_q_R@{i | } {A : Type@{i}} {x y : A}
  : forall (p : Path@{i} x y) (q : Path@{i} y x),
    Path@{i} idpath (conc p q) -> Path@{i} (inv p) q.
Proof.
  move=> p q.
  refine (let t := _ in t q).
  refine (match p
    as p'
    in Path _ y'
    return forall q' : Path@{i} y' x,
      Path idpath (conc p' q') -> Path (inv p') q'
    with idpath => _
  end).

  move=> q' path_1_c1q'.
  refine_conc (conc idpath q').
  -
    simpl inv.
    exact path_1_c1q'.
  -
  exact (conc_1_p q').
Defined.

(** Path_trpt_p_u_v です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L300 *)
Definition path_trpt_p_u_v@{i j | } {A : Type@{i}} (P : A -> Type@{j}) {x y : A}
  : forall (p : Path@{i} x y) (u : P x) (v : P y),
    Path@{j} u (trpt (inv p) v) -> Path@{j} (trpt p u) v.
Proof.
  move=> p u v.
  refine (let t := _ in t v).
  refine (match p
    as p'
    in Path _ y'
    return forall v' : P y',
      Path@{j} u (trpt (inv p') v') -> Path@{j} (trpt p' u) v'
    with idpath => _
  end).

  move=> v'.
  cbv.
  exact idmap.
Defined.

(** Path_trpt_inv_p_u_v です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L308 *)
Definition path_trpt_vp_u_v@{i j | } {A : Type@{i}} (P : A -> Type@{j}) {x y : A}
  : forall (p : Path@{i} y x) (u : P x) (v : P y),
    Path@{j} u (trpt p v) -> Path@{j} (trpt (inv p) u) v.
Proof.
  move=> p u v.
  refine (let t := _ in t u).
  refine (match p
    as p'
    in Path _ x'
    return forall u' : P x',
      Path@{j} u' (trpt p' v) -> Path@{j} (trpt (inv p') u') v
    with idpath => _
  end).

  move=> u'.
  cbv.
  exact idmap.
Defined.

(** Path_u_trpt_inv_p_v です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L316 *)
Definition path_u_trpt_vp_v@{i j | } {A : Type@{i}} (P : A -> Type@{j}) {x y : A}
  : forall (p : Path@{i} x y) (u : P x) (v : P y),
    Path@{j} (trpt p u) v -> Path@{j} u (trpt (inv p) v).
Proof.
  move=> p u v.
  refine (let t := _ in t v).
  refine (match p
    as p'
    in Path _ y'
    return forall v' : P y',
      Path@{j} (trpt p' u) v' -> Path@{j} u (trpt (inv p') v')
    with idpath => _
  end).

  move=> v'.
  cbv.
  exact idmap.
Defined.

(** Path_u_trpt_p_v です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L324 *)
Definition path_u_trpt_p_v@{i j | } {A : Type@{i}} (P : A -> Type@{j}) {x y : A}
  : forall (p : Path@{i} y x) (u : P x) (v : P y),
    Path@{j} (trpt (inv p) u) v -> Path@{j} u (trpt p v).
Proof.
  move=> p u v.
  refine (let t := _ in t u).
  refine (match p
    as p'
    in Path _ x'
    return forall u' : P x',
      Path@{j} (trpt (inv p') u') v -> Path@{j} u' (trpt p' v)
    with idpath => _
  end).

  move=> u'.
  cbv.
  exact idmap.
Defined.

(** inv_'path_trpt_p_u_v'_P_p_u_v_q です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L333 *)
Definition inv_'path_trpt_p_u_v'_P_p_u_v_q@{i j | }
  {A : Type@{i}} (P : A -> Type@{j}) {x y : A}
  (p : Path@{i} x y) (u : P x) (v : P y)
  : forall q : Path@{j} u (trpt (inv p) v),
    Path@{j}
      (inv (path_trpt_p_u_v P p u v q))
      (path_u_trpt_p_v P p v u (inv q)).
Proof.
  move=> q.
  refine (let t := _ in t v q).
  refine (match p
    as p'
    in Path _ y'
    return forall (v' : P y') (q' : Path@{j} u (trpt (inv p') v')),
      Path@{j}
        (inv (path_trpt_p_u_v P p' u v' q'))
        (path_u_trpt_p_v P p' v' u (inv q'))
    with idpath => _
  end).

  simpl trpt.
  move=> v' q'.
  simpl path_trpt_p_u_v.
  simpl path_u_trpt_p_v.
  unfold idmap.
  exact idpath.
Defined.

(** inv_'path_trpt_vp_u_v'_P_p_u_v_q です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L340 *)
Definition inv_'path_trpt_vp_u_v'_P_p_u_v_q@{i j | }
  {A : Type@{i}} (P : A -> Type@{j}) {x y : A}
  (p : Path@{i} y x) (u : P x) (v : P y)
  : forall q : Path@{j} u (trpt p v),
    Path@{j}
      (inv (path_trpt_vp_u_v P p u v q))
      (path_u_trpt_vp_v P p v u (inv q)).
Proof.
  move=> q.
  refine (let t := _ in t u q).
  refine (match p
    as p'
    in Path _ x'
    return forall (u' : P x') (q' : Path@{j} u' (trpt p' v)),
      Path@{j}
        (inv (path_trpt_vp_u_v P p' u' v q'))
        (path_u_trpt_vp_v P p' v u' (inv q'))
    with idpath => _
  end).

  simpl trpt.
  move=> u' q'.
  simpl path_trpt_vp_u_v.
  simpl path_u_trpt_vp_v.
  unfold idmap.
  exact idpath.
Defined.

(** inv_'path_u_trpt_vp_v'_P_p_u_v_q です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L347 *)
Definition inv_'path_u_trpt_vp_v'_P_p_u_v_q@{i j | }
  {A : Type@{i}} (P : A -> Type@{j}) {x y : A}
  (p : Path@{i} x y) (u : P x) (v : P y)
  : forall q : Path@{j} (trpt p u) v,
    Path@{j}
      (inv (path_u_trpt_vp_v P p u v q))
      (path_trpt_vp_u_v P p v u (inv q)).
Proof.
  move=> q.
  refine (let t := _ in t v q).
  refine (match p
    as p'
    in Path _ y'
    return forall (v' : P y') (q' : Path@{j} (trpt p' u) v'),
      Path@{j}
        (inv (path_u_trpt_vp_v P p' u v' q'))
        (path_trpt_vp_u_v P p' v' u (inv q'))
    with idpath => _
  end).

  simpl trpt.
  move=> v' q'.
  simpl path_u_trpt_vp_v.
  simpl path_trpt_vp_u_v.
  unfold idmap.
  exact idpath.
Defined.

(** inv_'path_u_trpt_p_v'_P_p_u_v_q です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L354 *)
Definition inv_'path_u_trpt_p_v'_P_p_u_v_q@{i j | }
  {A : Type@{i}} (P : A -> Type@{j}) {x y : A}
  (p : Path@{i} y x) (u : P x) (v : P y)
  : forall q : Path@{j} (trpt (inv p) u) v,
    Path@{j}
      (inv (path_u_trpt_p_v P p u v q))
      (path_trpt_p_u_v P p v u (inv q)).
Proof.
  move=> q.
  refine (let t := _ in t u q).
  refine (match p
    as p'
    in Path _ x'
    return forall (u' : P x') (q' : Path@{j} (trpt (inv p') u') v),
      Path@{j}
        (inv (path_u_trpt_p_v P p' u' v q'))
        (path_trpt_p_u_v P p' v u' (inv q'))
    with idpath => _
  end).

  simpl trpt.
  move=> u' q'.
  simpl path_u_trpt_p_v.
  simpl path_trpt_p_u_v.
  unfold idmap.
  exact idpath.
Defined.
