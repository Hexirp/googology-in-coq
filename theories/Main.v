(* Run with -nois. *)

Require Import GiC.Base.

(** 帰納原理 (induction principle) を生成しないように設定します。 *)
Unset Elimination Schemes.

(** 宇宙多相 (universe polymorphism) について設定します。 *)
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

(** 宇宙 (universe) について表示するように設定します。 *)
Set Printing Universes.

(** conc_p_idpath です。 *)
Definition conc_p_1@{i} {A : Type@{i}} {x y : A}
  : forall p : Path@{i} x y, Path@{i} (conc p idpath) p
  := fun p => match p with idpath => idpath end.

(** conc_idpath_p です。 *)
Definition conc_1_p@{i} {A : Type@{i}} {x y : A}
  : forall p : Path@{i} x y, Path@{i} (conc idpath p) p
  := fun p => match p with idpath => idpath end.

(** conc_p_conc_q_r です。 *)
Definition conc_p_cqr@{i} {A : Type@{i}} {x y z w : A}
  : forall (p : Path@{i} x y) (q : Path@{i} y z) (r : Path@{i} z w),
    Path@{i} (conc p (conc q r)) (conc (conc p q) r)
  := fun p q r => match r
    with idpath => match q
      with idpath => match p
        with idpath => idpath
      end
    end
  end.

(** conc_conc_p_q_r です。 *)
Definition conc_cpq_r@{i} {A : Type@{i}} {x y z w : A}
  : forall (p : Path@{i} x y) (q : Path@{i} y z) (r : Path@{i} z w),
    Path@{i} (conc (conc p q) r) (conc p (conc q r))
  := fun p q r => match r
    with idpath => match q
      with idpath => match p
        with idpath => idpath
      end
    end
  end.

(** conc_p_inv_p です。 *)
Definition conc_p_vp@{i} {A : Type@{i}} {x y : A}
  : forall p : Path@{i} x y, Path@{i} (conc p (inv p)) idpath
  := fun p => match p with idpath => idpath end.

(** conc_inv_p_p です。 *)
Definition conc_vp_p@{i} {A : Type@{i}} {x y : A}
  : forall p : Path@{i} x y, Path@{i} (conc (inv p) p) idpath
  := fun p => match p with idpath => idpath end.

(** conc_inv_p_conc_p_q です。 *)
Definition conc_vp_cpq@{i} {A : Type@{i}} {x y z : A}
  : forall (p : Path@{i} x y) (q : Path@{i} y z),
    Path@{i} (conc (inv p) (conc p q)) q
  := fun p q => match q with idpath => match p with idpath => idpath end end.

(** conc_p_conc_inv_p_q です。 *)
Definition conc_p_cvpq@{i} {A : Type@{i}} {x y z : A}
  : forall (p : Path@{i} x y) (q : Path@{i} x z),
    Path@{i} (conc p (conc (inv p) q)) q
  := fun p q => match q with idpath => match p with idpath => idpath end end.

(** conc_conc_p_q_inv_q です。 *)
Definition conc_cpq_vq@{i} {A : Type@{i}} {x y z : A}
  : forall (p : Path@{i} x y) (q : Path@{i} y z),
    Path@{i} (conc (conc p q) (inv q)) p
  := fun p q => match q with idpath => match p with idpath => idpath end end.

(** conc_conc_p_inv_q_q です。 *)
Definition conc_cpvq_q@{i} {A : Type@{i}} {x y z : A}
  : forall (p : Path@{i} x z) (q : Path@{i} y z),
    Path@{i} (conc (conc p (inv q)) q) p
  := fun p q => let
    t := match q
      as q'
      in Path _ z'
      return forall p' : Path@{i} x z',
        Path@{i} (conc (conc p' (inv q')) q') p'
      with idpath => fun p' => match p' with idpath => idpath end
    end
  in
    t p.

(** inv_conc_p_q です。 *)
Definition inv_cpq@{i} {A : Type@{i}} {x y z : A}
  : forall (p : Path@{i} x y) (q : Path@{i} y z),
    Path@{i} (inv (conc p q)) (conc (inv q) (inv p))
  := fun p q => match q with idpath => match p with idpath => idpath end end.

(** inv_conc_inv_p_q です。 *)
Definition inv_cvpq@{i} {A : Type@{i}} {x y z : A}
  : forall (p : Path@{i} x y) (q : Path@{i} x z),
    Path@{i} (inv (conc (inv p) q)) (conc (inv q) p)
  := fun p q => match q with idpath => match p with idpath => idpath end end.

(** inv_conc_p_inv_q です。 *)
Definition inv_cpvq@{i} {A : Type@{i}} {x y z : A}
  : forall (p : Path@{i} x z) (q : Path@{i} y z),
    Path@{i} (inv (conc p (inv q))) (conc q (inv p))
  := fun p q => let
    t := match q
      as q'
      in Path _ z'
      return forall p' : Path@{i} x z',
        Path@{i} (inv (conc p' (inv q'))) (conc q' (inv p'))
      with idpath => fun p' => match p' with idpath => idpath end
    end
  in
    t p.

(** inv_conc_inv_p_inv_q です。 *)
Definition inv_cvpvq@{i} {A : Type@{i}} {x y z : A}
  : forall (p : Path@{i} y x) (q : Path@{i} z y),
    Path@{i} (inv (conc (inv p) (inv q))) (conc q p)
  := fun p q => match p with idpath => match q with idpath => idpath end end.

(** inv_inv_p です。 *)
Definition inv_vp@{i} {A : Type@{i}} {x y z : A}
  : forall p : Path@{i} x y, Path@{i} (inv (inv p)) p
  := fun p => match p with idpath => idpath end.

Declare ML Module "ltac_plugin".
Declare ML Module "ssrmatching_plugin".
Declare ML Module "ssreflect_plugin".

Set Default Proof Mode "Classic".

(** Path_conc_r_p_q です。 *)
Definition path_crp_q_L@{i} {A : Type@{i}} {x y z : A}
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
  refine (conc _ (_ : Path@{i} p' _)).
  -
    exact (conc_1_p p').
  -
  refine (conc _ (_ : Path@{i} (conc (inv idpath) q) _)).
  +
    exact path_p'_cv1q.
  +
  simpl inv.
  exact (conc_1_p q).
Defined.

(** Path_conc_r_p_q です。 *)
Definition path_crp_q_R@{i} {A : Type@{i}} {x y z : A}
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
  refine (conc _ (_ : Path@{i} r _)).
  -
    exact (conc_p_1 r).
  -
  refine (conc _ (_ : Path@{i} (conc q' (inv idpath)) _)).
  +
    exact path_r_cq'v1.
  +
  simpl inv.
  exact (conc_p_1 q').
Defined.

(** Path_conc_inv_r_p_q です。 *)
Definition path_cvrp_q@{i} {A : Type@{i}} {x y z : A}
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
  refine (conc _ (_ : Path@{i} p _)).
  -
    simpl inv.
    exact (conc_1_p p).
  -
  refine (conc _ (_ : Path@{i} (conc idpath q') _)).
  +
    exact path_p_c1q'.
  +
  exact (conc_1_p q').
Defined.

(** Path_conc_r_inv_p_q です。 *)
Definition path_crvp_q@{i} {A : Type@{i}} {x y z : A}
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
  refine (conc _ (_ : Path@{i} r' _)).
  -
    simpl inv.
    exact (conc_p_1 r').
  -
  refine (conc _ (_ : Path@{i} (conc q idpath) _)).
  +
    exact path_r'_cq1.
  +
  exact (conc_p_1 q).
Defined.

(** Path_q_conc_r_p です。 *)
Definition path_q_crp_L@{i} {A : Type@{i}} {x y z : A}
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
  refine (conc _ (_ : Path@{i} (conc (inv idpath) q) _)).
  -
    simpl inv.
    exact (inv (conc_1_p q)).
  -
  refine (conc _ (_ : Path@{i} p' _)).
  +
    exact path_cv1q_p'.
  +
  exact (inv (conc_1_p p')).
Defined.

(** Path_q_conc_r_p です。 *)
Definition path_q_crp_R@{i} {A : Type@{i}} {x y z : A}
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
  refine (conc _ (_ : Path@{i} (conc q' (inv idpath)) _)).
  -
    simpl inv.
    exact (inv (conc_1_p q')).
  -
  refine (conc _ (_ : Path@{i} r _)).
  +
    exact path_cq'v1_r.
  +
  exact (inv (conc_p_1 r)).
Defined.

(** Path_q_conc_inv_r_p です。 *)
Definition path_q_cvrp@{i} {A : Type@{i}} {x y z : A}
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
  refine (conc _ (_ : Path@{i} (conc idpath q') _)).
  -
    exact (inv (conc_1_p q')).
  -
  refine (conc _ (_ : Path@{i} p _)).
  +
    exact path_c1q'_p.
  +
  simpl inv.
  exact (inv (conc_p_1 p)).
Defined.

(** Path_q_conc_r_inv_p です。 *)
Definition path_q_crvp@{i} {A : Type@{i}} {x y z : A}
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
  refine (conc _ (_ : Path@{i} (conc q idpath) _)).
  -
    exact (inv (conc_p_1 q)).
  -
  refine (conc _ (_ : Path@{i} r' _)).
  +
    exact path_cq1_r'.
  +
  simpl inv.
  exact (inv (conc_p_1 r')).
Defined.

(* Path_p_q です。 *)
Definition path_p_q_L_L@{i} {A : Type@{i}} {x y : A}
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
  refine (conc _ (_ : Path@{i} (conc p' (inv idpath)) _)).
  -
    simpl inv.
    exact (inv (conc_p_1 p')).
  -
  exact path_cp'v1_1.
Defined.

(* Path_p_q です。 *)
Definition path_p_q_L_R@{i} {A : Type@{i}} {x y : A}
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
  refine (conc _ (_ : Path@{i} (conc (inv idpath) p') _)).
  -
    simpl inv.
    exact (inv (conc_1_p p')).
  -
  exact path_cv1p'_1.
Defined.

(* Path_p_inv_q です。 *)
Definition path_p_vq_L@{i} {A : Type@{i}} {x y : A}
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
  refine (conc _ (_ : Path@{i} (conc p' idpath) _)).
  -
    exact (inv (conc_p_1 p')).
  -
  simpl inv.
  exact path_cp'1_1.
Defined.

(* Path_p_inv_q です。 *)
Definition path_p_vq_R@{i} {A : Type@{i}} {x y : A}
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
  refine (conc _ (_ : Path@{i} (conc idpath p') _)).
  -
    exact (inv (conc_1_p p')).
  -
  simpl inv.
  exact path_c1p'_1.
Defined.

(* Path_p_q です。 *)
Definition path_p_q_R_L@{i} {A : Type@{i}} {x y : A}
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
  refine (conc _ (_ : Path@{i} (conc (inv idpath) q') _)).
  -
    exact path_1_cv1q'.
  -
  simpl inv.
  exact (conc_1_p q').
Defined.

(* Path_p_q です。 *)
Definition path_p_q_R_R@{i} {A : Type@{i}} {x y : A}
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
  refine (conc _ (_ : Path@{i} (conc q' (inv idpath)) _)).
  -
    exact path_1_cq'v1.
  -
  simpl inv.
  exact (conc_p_1 q').
Defined.

(* Path_inv_p_q です。 *)
Definition path_vp_q_L@{i} {A : Type@{i}} {x y : A}
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
  refine (conc _ (_ : Path@{i} (conc q' idpath) _)).
  -
    simpl inv.
    exact path_1_cq'1.
  -
  exact (conc_p_1 q').
Defined.

(* Path_inv_p_q です。 *)
Definition path_vp_q_R@{i} {A : Type@{i}} {x y : A}
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
  refine (conc _ (_ : Path@{i} (conc idpath q') _)).
  -
    simpl inv.
    exact path_1_c1q'.
  -
  exact (conc_1_p q').
Defined.

(** Path_trpt_p_u_v です。 *)
Definition path_tpu_v@{i j} {A : Type@{i}} (P : A -> Type@{j}) {x y : A}
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
  simpl trpt.
  exact idmap.
Defined.

(** Path_trpt_inv_p_u_v です。 *)
Definition path_tvpu_v@{i j} {A : Type@{i}} (P : A -> Type@{j}) {x y : A}
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
  simpl trpt.
  exact idmap.
Defined.

(** Path_u_trpt_inv_p_v です。 *)
Definition path_u_tvpv@{i j} {A : Type@{i}} (P : A -> Type@{j}) {x y : A}
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
  simpl trpt.
  exact idmap.
Defined.

(** Path_u_trpt_p_v です。 *)
Definition path_u_tpv@{i j} {A : Type@{i}} (P : A -> Type@{j}) {x y : A}
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
  simpl trpt.
  exact idmap.
Defined.
