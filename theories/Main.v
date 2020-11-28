(* Run with -nois. *)

(** * 道についてのモジュール *)

Require Import GiC.Base.

(** 帰納原理 (induction principle) を生成しないように設定します。 *)
Unset Elimination Schemes.

(** 宇宙多相 (universe polymorphism) について設定します。 *)
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

(** 宇宙 (universe) について表示するように設定します。 *)
Set Printing Universes.

(** タクティックが使用できるように設定します。 *)
Set Default Proof Mode "Classic".

(** ** 汎用的な関数の定義 *)

(** 関数と関数の合成です。 *)
Definition compNN@{i j k | }
  {A : Type@{i}} {B : Type@{j}} {C : Type@{k}}
  : (B -> C) -> (A -> B) -> A -> C
  := comp.

(** 関数と依存関数の合成です。 *)
Definition compND@{i j k | }
  {A : Type@{i}} {B : A -> Type@{j}} {C : Type@{k}}
  : (forall a : A, B a -> C) -> (forall a : A, B a) -> A -> C
  := fun f g x => f x (g x).

(** 依存関数と関数の合成です。 *)
Definition compDN@{i j k | }
  {A : Type@{i}} {B : Type@{j}} {C : B -> Type@{k}}
  : (forall b : B, C b) -> forall (g : A -> B) (a : A), C (g a)
  := compD.

(** 依存関数と依存関数の合成です。 *)
Definition compDD@{i j k | }
  {A : Type@{i}} {B : A -> Type@{j}} {C : forall a : A, B a -> Type@{k}}
  : (forall (a : A) (b : B a), C a b) ->
    forall (g : forall a : A, B a) (a : A), C a (g a)
  := fun f g x => f x (g x).

(** 依存型に対応する ap です。 *)
Definition apD@{i j | }
  {A : Type@{i}} {B : A -> Type@{j}} (f : forall x : A, B x)
  {x y : A} (p : Path@{i} x y)
  : Path@{j} (trpt p (f x)) (f y)
  := match p with idpath => idpath end.

(** 一変数関数に対する ap です。 *)
Definition ap1@{i j | }
  {A : Type@{i}} {B : Type@{j}} (f : A -> B) {x x' : A} (p : Path@{i} x x')
  : Path@{j} (f x) (f x')
  := ap f p.

(** 二変数関数に対する ap です。 *)
Definition ap2@{i j k | }
  {A : Type@{i}} {B : Type@{j}} {C : Type@{k}} (f : A -> B -> C)
  {x x' : A} (p : Path@{i} x x') {y y' : B} (q : Path@{j} y y')
  : Path@{k} (f x y) (f x' y')
  := match p with idpath => ap1 (f x) q end.

(** 三変数関数に対する ap です。 *)
Definition ap3@{i j k l | }
  {A : Type@{i}} {B : Type@{j}} {C : Type@{k}} {D : Type@{l}}
  (f : A -> B -> C -> D)
  {x x' : A} (p : Path@{i} x x')
  {y y' : B} (q : Path@{j} y y')
  {z z' : C} (r : Path@{k} z z')
  : Path@{l} (f x y z) (f x' y' z')
  := match p with idpath => ap2 (f x) q r end.

(** 関数の 0-道を値の 1-道に適用する関数です。 *)
Definition ap01@{i j | } {A : Type@{i}} {B : Type@{j}}
  (f : A -> B) {x x' : A} (pxx' : Path@{i} x x') : Path@{j} (f x) (f x')
  := ap f pxx'.

(** 関数の 1-道を値の 0-道に適用する関数です。 *)
Definition ap10@{i j mij | i <= mij, j <= mij} {A : Type@{i}} {B : Type@{j}}
  {f f' : A -> B} (pff' : Path@{mij} f f') (x : A) : Path@{j} (f x) (f' x)
  := match pff' with idpath => idpath end.

(** 依存関数の 1-道を値の 0-道に適用する関数です。 *)
Definition ap1D0@{i j mij | i <= mij, j <= mij}
  {A : Type@{i}} {B : A -> Type@{j}}
  {f f' : forall x : A, B x} (pff' : Path@{mij} f f') (x : A)
  : Path@{j} (f x) (f' x)
  := match pff' with idpath => idpath end.

(** 関数の 1-道を値の 1-道に適用する関数です。 *)
Definition ap11@{i j k | i <= k, j <= k} {A : Type@{i}} {B : Type@{j}}
  {f f' : A -> B} (pff' : Path@{k} f f') {x x' : A} (pxx' : Path@{i} x x')
  : Path@{j} (f x) (f' x)
  := match pxx' with idpath => match pff' with idpath => idpath end end.

(** ** 1-次元の亜群構造 *)

(** conc_p_idpath です。 *)
Definition conc_p_1@{i | } {A : Type@{i}} {x y : A}
  : forall p : Path@{i} x y, Path@{i} (conc p idpath) p
  := fun p => match p with idpath => idpath end.

(** conc_idpath_p です。 *)
Definition conc_1_p@{i | } {A : Type@{i}} {x y : A}
  : forall p : Path@{i} x y, Path@{i} (conc idpath p) p
  := fun p => match p with idpath => idpath end.

(** conc_p_conc_q_r です。 *)
Definition conc_p_cqr@{i | } {A : Type@{i}} {x y z w : A}
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
Definition conc_cpq_r@{i | } {A : Type@{i}} {x y z w : A}
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
Definition conc_p_vp@{i | } {A : Type@{i}} {x y : A}
  : forall p : Path@{i} x y, Path@{i} (conc p (inv p)) idpath
  := fun p => match p with idpath => idpath end.

(** conc_inv_p_p です。 *)
Definition conc_vp_p@{i | } {A : Type@{i}} {x y : A}
  : forall p : Path@{i} x y, Path@{i} (conc (inv p) p) idpath
  := fun p => match p with idpath => idpath end.

(** conc_inv_p_conc_p_q です。 *)
Definition conc_vp_cpq@{i | } {A : Type@{i}} {x y z : A}
  : forall (p : Path@{i} x y) (q : Path@{i} y z),
    Path@{i} (conc (inv p) (conc p q)) q
  := fun p q => match q with idpath => match p with idpath => idpath end end.

(** conc_p_conc_inv_p_q です。 *)
Definition conc_p_cvpq@{i | } {A : Type@{i}} {x y z : A}
  : forall (p : Path@{i} x y) (q : Path@{i} x z),
    Path@{i} (conc p (conc (inv p) q)) q
  := fun p q => match q with idpath => match p with idpath => idpath end end.

(** conc_conc_p_q_inv_q です。 *)
Definition conc_cpq_vq@{i | } {A : Type@{i}} {x y z : A}
  : forall (p : Path@{i} x y) (q : Path@{i} y z),
    Path@{i} (conc (conc p q) (inv q)) p
  := fun p q => match q with idpath => match p with idpath => idpath end end.

(** conc_conc_p_inv_q_q です。 *)
Definition conc_cpvq_q@{i | } {A : Type@{i}} {x y z : A}
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
Definition inv_cpq@{i | } {A : Type@{i}} {x y z : A}
  : forall (p : Path@{i} x y) (q : Path@{i} y z),
    Path@{i} (inv (conc p q)) (conc (inv q) (inv p))
  := fun p q => match q with idpath => match p with idpath => idpath end end.

(** inv_conc_inv_p_q です。 *)
Definition inv_cvpq@{i | } {A : Type@{i}} {x y z : A}
  : forall (p : Path@{i} x y) (q : Path@{i} x z),
    Path@{i} (inv (conc (inv p) q)) (conc (inv q) p)
  := fun p q => match q with idpath => match p with idpath => idpath end end.

(** inv_conc_p_inv_q です。 *)
Definition inv_cpvq@{i | } {A : Type@{i}} {x y z : A}
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
Definition inv_cvpvq@{i | } {A : Type@{i}} {x y z : A}
  : forall (p : Path@{i} y x) (q : Path@{i} z y),
    Path@{i} (inv (conc (inv p) (inv q))) (conc q p)
  := fun p q => match p with idpath => match q with idpath => idpath end end.

(** inv_inv_p です。 *)
Definition inv_vp@{i | } {A : Type@{i}} {x y : A}
  : forall p : Path@{i} x y, Path@{i} (inv (inv p)) p
  := fun p => match p with idpath => idpath end.

(** *** 移項のための補題 *)

(** Path_conc_r_p_q です。 *)
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

(** Path_p_q です。 *)
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
  refine (conc _ (_ : Path@{i} (conc p' (inv idpath)) _)).
  -
    simpl inv.
    exact (inv (conc_p_1 p')).
  -
  exact path_cp'v1_1.
Defined.

(** Path_p_q です。 *)
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
  refine (conc _ (_ : Path@{i} (conc (inv idpath) p') _)).
  -
    simpl inv.
    exact (inv (conc_1_p p')).
  -
  exact path_cv1p'_1.
Defined.

(** Path_p_inv_q です。 *)
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
  refine (conc _ (_ : Path@{i} (conc p' idpath) _)).
  -
    exact (inv (conc_p_1 p')).
  -
  simpl inv.
  exact path_cp'1_1.
Defined.

(** Path_p_inv_q です。 *)
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
  refine (conc _ (_ : Path@{i} (conc idpath p') _)).
  -
    exact (inv (conc_1_p p')).
  -
  simpl inv.
  exact path_c1p'_1.
Defined.

(** Path_p_q です。 *)
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
  refine (conc _ (_ : Path@{i} (conc (inv idpath) q') _)).
  -
    exact path_1_cv1q'.
  -
  simpl inv.
  exact (conc_1_p q').
Defined.

(** Path_p_q です。 *)
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
  refine (conc _ (_ : Path@{i} (conc q' (inv idpath)) _)).
  -
    exact path_1_cq'v1.
  -
  simpl inv.
  exact (conc_p_1 q').
Defined.

(** Path_inv_p_q です。 *)
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
  refine (conc _ (_ : Path@{i} (conc q' idpath) _)).
  -
    simpl inv.
    exact path_1_cq'1.
  -
  exact (conc_p_1 q').
Defined.

(** Path_inv_p_q です。 *)
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
  refine (conc _ (_ : Path@{i} (conc idpath q') _)).
  -
    simpl inv.
    exact path_1_c1q'.
  -
  exact (conc_1_p q').
Defined.

(** Path_trpt_p_u_v です。 *)
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
  simpl trpt.
  exact idmap.
Defined.

(** Path_trpt_inv_p_u_v です。 *)
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
  simpl trpt.
  exact idmap.
Defined.

(** Path_u_trpt_inv_p_v です。 *)
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
  simpl trpt.
  exact idmap.
Defined.

(** Path_u_trpt_p_v です。 *)
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
  simpl trpt.
  exact idmap.
Defined.

(** inv_'path_trpt_p_u_v'_P_p_u_v_q です。 *)
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

(** *** 関手としての関数 *)

(** ap_f_idpath です。 *)
Definition ap_f_1@{i j | } {A : Type@{i}} {B : Type@{j}} (f : A -> B) (x : A)
  : Path@{j} (ap f (idpath x)) (idpath (f x)).
Proof.
  simpl ap.
  exact idpath.
Defined.

(** apD_f_idpath です。 *)
Definition apD_f_1@{i j | }
  {A : Type@{i}} {B : A -> Type@{j}} (f : forall x : A, B x) (x : A)
  : Path@{j} (apD f (idpath x)) (idpath (f x)).
Proof.
  simpl apD.
  exact idpath.
Defined.

(** ap_f_conc_p_q です。 *)
Definition ap_f_cpq@{i j | }
  {A : Type@{i}} {B : Type@{j}} (f : A -> B) {x y z : A}
  : forall (p : Path@{i} x y) (q : Path@{i} y z),
    Path@{j} (ap f (conc p q)) (conc (ap f p) (ap f q)).
Proof.
  move=> p q.
  refine (match q with idpath => _ end).
  refine (match p with idpath => _ end).
  simpl ap.
  simpl conc.
  exact idpath.
Defined.

(** conc_r_ap_f_conc_p_q です。 *)
Definition conc_r_ap_f_cpq@{i j | }
  {A : Type@{i}} {B : Type@{j}} (f : A -> B) {w : B} {x y z : A}
  : forall (r : Path@{j} w (f x)) (p : Path@{i} x y) (q : Path@{i} y z),
    Path@{j} (conc r (ap f (conc p q))) (conc (conc r (ap f p)) (ap f q)).
Proof.
  move=> r p q.
  refine (match q with idpath => _ end).
  refine (match p with idpath => _ end).
  simpl ap.
  change (Path@{j} (conc r (conc idpath idpath)) (conc (conc r idpath) idpath)).
  exact (conc_p_cqr r idpath idpath).
Defined.

(** conc_ap_f_conc_p_q_r です。 *)
Definition conc_ap_f_cpq_r@{i j | }
  {A : Type@{i}} {B : Type@{j}} (f : A -> B) {x y z : A} {w : B}
  : forall (p : Path@{i} x y) (q : Path@{i} y z) (r : Path@{j} (f z) w),
    Path@{j} (conc (ap f (conc p q)) r) (conc (ap f p) (conc (ap f q) r)).
Proof.
  move=> p q r.
  refine (let t := _ in t r).
  refine (match q
    as q'
    in Path _ z'
    return forall r' : Path@{j} (f z') w,
      Path@{j} (conc (ap f (conc p q')) r') (conc (ap f p) (conc (ap f q') r'))
    with idpath => _
  end).
  refine (match p
    as p'
    in Path _ y'
    return forall r' : Path@{j} (f y') w,
      Path@{j}
        (conc (ap f (conc p' idpath)) r')
        (conc (ap f p') (conc (ap f idpath) r'))
    with idpath => _
  end).
  move=> r'.
  simpl ap.
  change (Path@{j} (conc (conc idpath idpath) r') (conc idpath (conc idpath r'))).
  exact (conc_cpq_r idpath idpath r').
Defined.

(** inv_ap_f_p です。 *)
Definition inv_ap_f_p@{i j | }
  {A : Type@{i}} {B : Type@{j}} (f : A -> B) {x y : A}
  : forall p : Path@{i} x y, Path@{j} (inv (ap f p)) (ap f (inv p)).
Proof.
  move=> p.
  refine (match p with idpath => _ end).
  simpl ap.
  simpl inv.
  exact idpath.
Defined.

(** ap_f_inv_p です。 *)
Definition ap_f_vp@{i j | }
  {A : Type@{i}} {B : Type@{j}} (f : A -> B) {x y : A}
  : forall p : Path@{i} x y, Path@{j} (ap f (inv p)) (inv (ap f p)).
Proof.
  move=> p.
  refine (match p with idpath => _ end).
  simpl ap.
  simpl inv.
  exact idpath.
Defined.

(** ap_idmap_p です。 *)
Definition ap_idmap_p@{i | }
  {A : Type@{i}} {x y : A}
  : forall p : Path@{i} x y, Path@{i} (ap idmap p) p.
Proof.
  move=> p.
  refine (match p with idpath => _ end).
  simpl ap.
  exact idpath.
Defined.

(** ap_comp_f_g_p です。 *)
Definition ap_cfg_p@{i j k | }
  {A : Type@{i}} {B : Type@{j}} {C : Type@{k}}
  (f : B -> C) (g : A -> B) {x y : A}
  : forall p : Path@{i} x y, Path@{k} (ap (comp f g) p) (ap f (ap g p)).
Proof.
  move=> p.
  refine (match p with idpath => _ end).
  simpl ap.
  exact idpath.
Defined.

(** ap_lam_a_f_g_x_p です。 *)
Definition ap_lam_x_f_g_x_p@{i j k | }
  {A : Type@{i}} {B : Type@{j}} {C : Type@{k}}
  (f : B -> C) (g : A -> B) {x y : A}
  : forall p : Path@{i} x y,
    Path@{k} (ap (fun x : A => f (g x)) p) (ap f (ap g p)).
Proof.
  move=> p.
  refine (match p with idpath => _ end).
  simpl ap.
  exact idpath.
Defined.

(** ap_const_z_p です。 *)
Definition ap_const_z_p@{i j | }
  {A : Type@{i}} {B : Type@{j}} {x y : A} (z : B)
  : forall p : Path@{i} x y, Path@{j} (ap (const z) p) idpath.
Proof.
  move=> p.
  refine (match p with idpath => _ end).
  simpl ap.
  exact idpath.
Defined.

(** ap_lam_x_z_p です。 *)
Definition ap_lam_a_z_p@{i j | }
  {A : Type@{i}} {B : Type@{j}} {x y : A} (z : B)
  : forall p : Path@{i} x y, Path@{j} (ap (fun x : A => z) p) idpath.
Proof.
  move=> p.
  refine (match p with idpath => _ end).
  simpl ap.
  exact idpath.
Defined.

(** Path_conc_ap_f_q_p_y_conc_p_x_ap_g_q です。 *)
Definition path_conc_afq_py_conc_px_agq@{i j | }
  {A : Type@{i}} {B : Type@{j}} {f g : A -> B}
  (p : forall x : A, Path@{j} (f x) (g x)) {x y : A}
  : forall q : Path@{i} x y,
    Path@{j} (conc (ap f q) (p y)) (conc (p x) (ap g q)).
Proof.
  move=> q.
  refine (match q with idpath => _ end).
  simpl ap.
  refine (conc _ (_ : Path@{j} (p x) _)).
  -
    exact (conc_1_p (p x)).
  -
    exact (inv (conc_p_1 (p x))).
Defined.

(** Path_ap_f_q_conc_conc_p_x_ap_g_q_inv_p_y です。 *)
Definition path_afq_conc_conc_px_agq_inv_py@{i j | }
  {A : Type@{i}} {B : Type@{j}} {f g : A -> B}
  (p : forall x : A, Path@{j} (f x) (g x)) {x y : A}
  : forall q : Path@{i} x y,
    Path@{j} (ap f q) (conc (conc (p x) (ap g q)) (inv (p y))).
Proof.
  move=> q.
  refine (path_q_crvp (p y) (ap f q) (conc (p x) (ap g q)) _).
  exact (path_conc_afq_py_conc_px_agq p q).
Defined.

(** Path_conc_p_x_ap_f_q_conc_ap_g_q_p_y です。 *)
Definition path_conc_px_afq_conc_agq_py@{i j | }
  {A : Type@{i}} {B : Type@{j}} {f g : A -> B}
  (p : forall x : A, Path@{j} (g x) (f x)) {x y : A}
  : forall q : Path@{i} x y,
    Path@{j} (conc (p x) (ap f q)) (conc (ap g q) (p y)).
Proof.
  move=> q.
  refine (match q with idpath => _ end).
  simpl ap.
  refine (conc _ (_ : Path@{j} (p x) _)).
  -
    exact (conc_1_p (p x)).
  -
    exact (inv (conc_p_1 (p x))).
Defined.

(** Path_conc_ap_f_q_p_y_conc_p_x_q です。 *)
Definition path_conc_afq_py_conc_px_q@{i | }
  {A : Type@{i}} {f : A -> A} (p : forall x : A, Path@{i} (f x) x) {x y : A}
  : forall q : Path@{i} x y, Path@{i} (conc (ap f q) (p y)) (conc (p x) q).
Proof.
  move=> q.
  refine (match q with idpath => _ end).
  simpl ap.
  refine (conc _ (_ : Path@{i} (p x) _)).
  -
    exact (conc_1_p (p x)).
  -
    exact (inv (conc_p_1 (p x))).
Defined.

(** Path_conc_ap_f_q_p_y_conc_p_x_q です。 *)
Definition path_afq_conc_conc_px_q_inv_py@{i | }
  {A : Type@{i}} {f : A -> A} (p : forall x : A, Path@{i} (f x) x) {x y : A}
  : forall q : Path@{i} x y, Path@{i} (ap f q) (conc (conc (p x) q) (inv (p y))).
Proof.
  move=> q.
  refine (path_q_crvp (p y) (ap f q) (conc (p x) q) _).
  exact (path_conc_afq_py_conc_px_q p q).
Defined.

(** Path_conc_p_x_ap_f_q_conc_q_p_y です。 *)
Definition path_conc_px_afq_conc_q_py@{i | }
  {A : Type@{i}} {f : A -> A} (p : forall x : A, Path@{i} x (f x)) {x y : A}
  : forall q : Path@{i} x y, Path@{i} (conc (p x) (ap f q)) (conc q (p y)).
Proof.
  move=> q.
  refine (match q with idpath => _ end).
  simpl ap.
  refine (conc _ (_ : Path@{i} (p x) _)).
  -
    exact (conc_p_1 (p x)).
  -
    exact (inv (conc_1_p (p x))).
Defined.

(** Path_conc_conc_r_ap_f_q_conc_p_y_s_conc_conc_r_p_x_conc_ap_g_q_s です。 *)
Definition path_conc_crA_cPs_conc_crP_cAs@{i j | }
  {A : Type@{i}} {B : Type@{j}} {f g : A -> B}
  (p : forall x : A, Path@{j} (f x) (g x)) {x y : A}
  (q : Path@{i} x y) {z w : B} (r : Path@{j} z (f x)) (s : Path@{j} (g y) w)
  : Path@{j}
    (conc (conc r (ap f q)) (conc (p y) s))
    (conc (conc r (p x)) (conc (ap g q) s)).
Proof.
  refine (match s with idpath => _ end).
  refine (match q with idpath => _ end).
  simpl ap.
  refine (conc _ (_ : Path@{j} (conc r (p x)) _)).
  -
    refine (ap2 conc _ _).
    +
      exact (conc_p_1 r).
    +
      exact (conc_p_1 (p x)).
  -
    change (Path@{j} (conc r (p x)) (conc (conc r (p x)) idpath)).
    exact (inv (conc_p_1 (conc r (p x)))).
Defined.

(** Path_conc_conc_r_ap_f_q_p_y_conc_conc_r_p_x_ap_g_q です。 *)
Definition path_conc_crA_P_conc_crP_A@{i j | }
  {A : Type@{i}} {B : Type@{j}} {f g : A -> B}
  (p : forall x : A, Path@{j} (f x) (g x)) {x y : A}
  (q : Path@{i} x y) {z : B} (r : Path@{j} z (f x))
  : Path@{j}
    (conc (conc r (ap f q)) (p y))
    (conc (conc r (p x)) (ap g q)).
Proof.
  refine (match q with idpath => _ end).
  simpl ap.
  refine (conc _ (_ : Path@{j} (conc r (p x)) _)).
  -
    refine (ap (fun pzfx => conc pzfx (p x)) _).
    exact (conc_p_1 r).
  -
    exact (inv (conc_p_1 (conc r (p x)))).
Defined.

(** Path_conc_ap_f_q_conc_p_y_s_conc_p_x_conc_ap_g_q_s です。 *)
Definition path_conc_A_cPs_conc_P_cAs@{i j | }
  {A : Type@{i}} {B : Type@{j}} {f g : A -> B}
  (p : forall x : A, Path@{j} (f x) (g x)) {x y : A}
  (q : Path@{i} x y) {w : B} (s : Path@{j} (g y) w)
  : Path@{j}
    (conc (ap f q) (conc (p y) s))
    (conc (p x) (conc (ap g q) s)).
Proof.
  refine (match s with idpath => _ end).
  refine (match q with idpath => _ end).
  simpl ap.
  refine (conc _ (_ : Path@{j} (p x) _)).
  -
    refine (conc _ (_ : Path@{j} (conc (p x) idpath) _)).
    +
      exact (conc_1_p (conc (p x) idpath)).
    +
      exact (conc_p_1 (p x)).
  -
    change (Path@{j} (p x) (conc (p x) idpath)).
    exact (inv (conc_p_1 (p x))).
Defined.

(** Path_conc_conc_r_ap_f_q_conc_p_y_s_conc_conc_r_p_x_conc_q_s です。 *)
Definition path_conc_crA_cPs_conc_crP_cqs@{i | }
  {A : Type@{i}} {f : A -> A}
  (p : forall x : A, Path@{i} (f x) x) {x y : A}
  (q : Path@{i} x y) {z w : A} (r : Path@{i} z (f x)) (s : Path@{i} y w)
  : Path@{i}
    (conc (conc r (ap f q)) (conc (p y) s))
    (conc (conc r (p x)) (conc q s)).
Proof.
  refine (match s with idpath => _ end).
  refine (match q with idpath => _ end).
  simpl ap.
  refine (conc _ (_ : Path@{i} (conc r (p x)) _)).
  -
    refine (ap2 conc _ _).
    +
      exact (conc_p_1 r).
    +
      exact (conc_p_1 (p x)).
  -
    change (Path@{i} (conc r (p x)) (conc (conc r (p x)) idpath)).
    exact (inv (conc_p_1 (conc r (p x)))).
Defined.

(** Path_conc_conc_r_q_conc_p_y_s_conc_conc_r_p_x_conc_ap_g_q_s です。 *)
Definition path_conc_crq_cPs_conc_crP_cAs@{i | }
  {A : Type@{i}} {g : A -> A}
  (p : forall x : A, Path@{i} x (g x)) {x y : A}
  (q : Path@{i} x y) {z w : A} (r : Path@{i} z x) (s : Path@{i} (g y) w)
  : Path@{i}
    (conc (conc r q) (conc (p y) s))
    (conc (conc r (p x)) (conc (ap g q) s)).
Proof.
  refine (match s with idpath => _ end).
  refine (match q with idpath => _ end).
  simpl ap.
  refine (conc _ (_ : Path@{i} (conc r (p x)) _)).
  -
    refine (ap2 conc _ _).
    +
      exact (conc_p_1 r).
    +
      exact (conc_p_1 (p x)).
  -
    change (Path@{i} (conc r (p x)) (conc (conc r (p x)) idpath)).
    exact (inv (conc_p_1 (conc r (p x)))).
Defined.

(** Path_conc_conc_r_ap_f_q_p_y_conc_conc_r_p_x_q です。 *)
Definition path_conc_crA_P_conc_crP_q@{i | }
  {A : Type@{i}} {f : A -> A}
  (p : forall x : A, Path@{i} (f x) x) {x y : A}
  (q : Path@{i} x y) {z : A} (r : Path@{i} z (f x))
  : Path@{i}
    (conc (conc r (ap f q)) (p y))
    (conc (conc r (p x)) q).
Proof.
  refine (match q with idpath => _ end).
  simpl ap.
  refine (conc _ (_ : Path@{i} (conc r (p x)) _)).
  -
    refine (ap (fun pzfx => conc pzfx (p x)) _).
    exact (conc_p_1 r).
  -
    exact (inv (conc_p_1 (conc r (p x)))).
Defined.

(** Path_conc_conc_r_q_p_y_conc_conc_r_p_x_ap_g_q です。 *)
Definition path_conc_crq_P_conc_crP_A@{i | }
  {A : Type@{i}} {g : A -> A}
  (p : forall x : A, Path@{i} x (g x)) {x y : A}
  (q : Path@{i} x y) {z : A} (r : Path@{i} z x)
  : Path@{i}
    (conc (conc r q) (p y))
    (conc (conc r (p x)) (ap g q)).
Proof.
  refine (match q with idpath => _ end).
  simpl ap.
  refine (conc _ (_ : Path@{i} (conc r (p x)) _)).
  -
    refine (ap (fun pzfx => conc pzfx (p x)) _).
    exact (conc_p_1 r).
  -
    exact (inv (conc_p_1 (conc r (p x)))).
Defined.

(** Path_conc_ap_f_q_conc_p_y_s_conc_p_x_conc_q_s です。 *)
Definition path_conc_A_cPs_conc_P_cqs@{i | }
  {A : Type@{i}} {f : A -> A}
  (p : forall x : A, Path@{i} (f x) x) {x y : A}
  (q : Path@{i} x y) {w : A} (s : Path@{i} y w)
  : Path@{i}
    (conc (ap f q) (conc (p y) s))
    (conc (p x) (conc q s)).
Proof.
  refine (match s with idpath => _ end).
  refine (match q with idpath => _ end).
  simpl ap.
  refine (conc _ (_ : Path@{i} (p x) _)).
  -
    refine (conc _ (_ : Path@{i} (conc (p x) idpath) _)).
    +
      exact (conc_1_p (conc (p x) idpath)).
    +
      exact (conc_p_1 (p x)).
  -
    change (Path@{i} (p x) (conc (p x) idpath)).
    exact (inv (conc_p_1 (p x))).
Defined.

(** Path_conc_q_conc_p_y_s_conc_p_x_conc_ap_g_q_s です。 *)
Definition path_conc_q_cPs_conc_P_cAs@{i | }
  {A : Type@{i}} {g : A -> A}
  (p : forall x : A, Path@{i} x (g x)) {x y : A}
  (q : Path@{i} x y) {w : A} (s : Path@{i} (g y) w)
  : Path@{i}
    (conc q (conc (p y) s))
    (conc (p x) (conc (ap g q) s)).
Proof.
  refine (match s with idpath => _ end).
  refine (match q with idpath => _ end).
  simpl ap.
  refine (conc _ (_ : Path@{i} (p x) _)).
  -
    refine (conc _ (_ : Path@{i} (conc (p x) idpath) _)).
    +
      exact (conc_1_p (conc (p x) idpath)).
    +
      exact (conc_p_1 (p x)).
  -
    change (Path@{i} (p x) (conc (p x) idpath)).
    exact (inv (conc_p_1 (p x))).
Defined.

(** path_conc_'conc_1_p'_p_q_ap_lam_r_conc_1_r_q です。 *)
Definition path_conc_'conc_1_p'_p_q_ap_lam_r_conc_1_r_q@{i | }
  {A : Type@{i}} {x : A} (p : Path@{i} x x) (q : Path@{i} p idpath)
  : Path@{i} (conc (conc_1_p p) q) (ap (fun r => conc idpath r) q).
Proof.
  refine (match inv_vp q
    as _
    in Path _ q'
    return Path@{i} (conc (conc_1_p p) q') (ap (fun r => conc idpath r) q')
    with idpath => _
  end).
  refine (match inv q
    as vq'
    in Path _ p'
    return Path@{i}
      (conc (conc_1_p p') (inv vq'))
      (ap (fun r => conc idpath r) (inv vq'))
    with idpath => _
  end).
  simpl ap.
  simpl conc.
  exact idpath.
Defined.

(** path_conc_'conc_p_1'_p_q_ap_lam_r_conc_r_1_q です。 *)
Definition path_conc_'conc_p_1'_p_q_ap_lam_r_conc_r_1_q@{i | }
  {A : Type@{i}} {x : A} (p : Path@{i} x x) (q : Path@{i} p idpath)
  : Path@{i} (conc (conc_p_1 p) q) (ap (fun r => conc r idpath) q).
Proof.
  refine (match inv_vp q
    as _
    in Path _ q'
    return Path@{i} (conc (conc_p_1 p) q') (ap (fun r => conc r idpath) q')
    with idpath => _
  end).
  refine (match inv q
    as vq'
    in Path _ p'
    return Path@{i}
      (conc (conc_p_1 p') (inv vq'))
      (ap (fun r => conc r idpath) (inv vq'))
    with idpath => _
  end).
  simpl ap.
  simpl conc.
  exact idpath.
Defined.

(** *** [ap10] についての定理 *)

(** ap10_idpath_x です。 *)
Definition ap10_1_x@{i j mij | i <= mij, j <= mij}
  {A : Type@{i}} {B : Type@{j}} (f : A -> B) (x : A)
  : Path@{j} (ap10 (idpath@{mij} f) x) (idpath (f x)).
Proof.
  simpl ap10.
  exact idpath.
Defined.

(** ap10_conc_p_q_x です。 *)
Definition ap10_cpq_x@{i j mij | i <= mij, j <= mij}
  {A : Type@{i}} {B : Type@{j}} {f f' f'' : A -> B}
  (pff' : Path@{mij} f f') (pf'f'' : Path@{mij} f' f'') (x : A)
  : Path@{j}
    (ap10 (conc pff' pf'f'') x)
    (conc (ap10 pff' x) (ap10 pf'f'' x)).
Proof.
  refine (match pf'f'' with idpath => _ end).
  refine (match pff' with idpath => _ end).
  simpl ap10.
  simpl conc.
  exact idpath.
Defined.

(** ap10_inv_p_x です。 *)
Definition ap10_vp_x@{i j mij | i <= mij, j <= mij}
  {A : Type@{i}} {B : Type@{j}} {f f' : A -> B}
  (pff' : Path@{mij} f f') (x : A)
  : Path@{j} (ap10 (inv pff') x) (inv (ap10 pff' x)).
Proof.
  refine (match pff' with idpath => _ end).
  simpl ap10.
  simpl inv.
  exact idpath.
Defined.

(** ap1D0_idpath_x です。 *)
Definition ap1D0_1_x@{i j mij | i <= mij, j <= mij}
  {A : Type@{i}} {B : A -> Type@{j}} (f : forall x : A, B x) (x : A)
  : Path@{j} (ap1D0 (idpath@{mij} f) x) (idpath (f x)).
Proof.
  simpl ap1D0.
  exact idpath.
Defined.

(** ap1D0_conc_p_q_x です。 *)
Definition ap1D0_cpq_x@{i j mij | i <= mij, j <= mij}
  {A : Type@{i}} {B : A -> Type@{j}} {f f' f'' : forall x : A, B x}
  (pff' : Path@{mij} f f') (pf'f'' : Path@{mij} f' f'') (x : A)
  : Path@{j}
    (ap1D0 (conc pff' pf'f'') x)
    (conc (ap1D0 pff' x) (ap1D0 pf'f'' x)).
Proof.
  refine (match pf'f'' with idpath => _ end).
  refine (match pff' with idpath => _ end).
  simpl ap1D0.
  simpl conc.
  exact idpath.
Defined.

(** ap1D0_inv_p_x です。 *)
Definition ap1D0_vp_x@{i j mij | i <= mij, j <= mij}
  {A : Type@{i}} {B : A -> Type@{j}} {f f' : forall x : A, B x}
  (pff' : Path@{mij} f f') (x : A)
  : Path@{j} (ap1D0 (inv pff') x) (inv (ap1D0 pff' x)).
Proof.
  refine (match pff' with idpath => _ end).
  simpl ap1D0.
  simpl inv.
  exact idpath.
Defined.

(** ap10_ap_lam_f_compNN_f_g_p_x です。 *)
Definition ap10_ap_lam_f_compNN_f_g_p_x
  @{i j k mjk mik | j <= mjk, k <= mjk, i <= mik, k <= mik}
  {A : Type@{i}} {B : Type@{j}} {C : Type@{k}} {f f' : B -> C} {g : A -> B}
  (pff' : Path@{mjk} f f') (x : A)
  : Path@{k}
    (ap10@{i k mik} (ap (fun f => compNN f g) pff') x)
    (ap10@{j k mjk} pff' (g x)).
Proof.
  refine (match pff' with idpath => _ end).
  simpl ap10.
  exact idpath.
Defined.

(** ap1D0_ap_lam_f_compDN_f_g_p_x です。 *)
Definition ap1D0_ap_lam_f_compDN_f_g_p_x
  @{i j k mjk mik | j <= mjk, k <= mjk, i <= mik, k <= mik}
  {A : Type@{i}} {B : Type@{j}} {C : B -> Type@{k}}
  {f f' : forall x : B, C x} {g : A -> B}
  (pff' : Path@{mjk} f f') (x : A)
  : Path@{k}
    (ap1D0@{i k mik} (ap (fun f => compDN f g) pff') x)
    (ap1D0@{j k mjk} pff' (g x)).
Proof.
  refine (match pff' with idpath => _ end).
  simpl ap1D0.
  exact idpath.
Defined.

(** ap10_ap_lam_g_compNN_f_g_p_x です。 *)
Definition ap10_ap_lam_g_compNN_f_g_p_x
  @{i j k mij mik | i <= mij, j <= mij, i <= mik, k <= mik}
  {A : Type@{i}} {B : Type@{j}} {C : Type@{k}} {f : B -> C} {g g' : A -> B}
  (pgg' : Path@{mij} g g') (x : A)
  : Path@{k}
    (ap10@{i k mik} (ap (fun g => compNN f g) pgg') x)
    (ap f (ap10@{i j mij} pgg' x)).
Proof.
  refine (match pgg' with idpath => _ end).
  simpl ap10.
  exact idpath.
Defined.

(** ap1D0_ap_lam_g_compND_f_g_p_x です。 *)
Definition ap1D0_ap_lam_g_compND_f_g_p_x
  @{i j k mij mik | i <= mij, j <= mij, i <= mik, k <= mik}
  {A : Type@{i}} {B : A -> Type@{j}} {C : Type@{k}}
  {f : forall x : A, B x -> C} {g g' : forall x : A, B x}
  (pgg' : Path@{mij} g g') (x : A)
  : Path@{k}
    (ap1D0@{i k mik} (ap (fun g => compND f g) pgg') x)
    (ap (f x) (ap1D0@{i j mij} pgg' x)).
Proof.
  refine (match pgg' with idpath => _ end).
  simpl ap1D0.
  simpl ap.
  exact idpath.
Defined.

(** *** 輸送と、道の亜群構造 *)

(** trpt_idpath_u です。 *)
Definition trpt_1_u@{i j | }
  {A : Type@{i}} (P : A -> Type@{j}) {x : A} (u : P x)
  : Path@{j} (trpt idpath u) u.
Proof.
  simpl trpt.
  exact idpath.
Defined.

(** trpt_conc_p_q_u です。 *)
Definition trpt_cpq_u@{i j | }
  {A : Type@{i}} (P : A -> Type@{j}) {x y z : A}
  (p : Path@{i} x y) (q : Path@{i} y z) (u : P x)
  : Path@{j} (trpt (conc p q) u) (trpt q (trpt p u)).
Proof.
  refine (match q with idpath => _ end).
  refine (match p with idpath => _ end).
  simpl trpt.
  exact idpath.
Defined.

(** trpt_p_trpt_inv_p_u です。 *)
Definition trpt_p_trpt_vp_u@{i j | }
  {A : Type@{i}} (P : A -> Type@{j}) {x y : A}
  (p : Path@{i} x y) (u : P y)
  : Path@{j} (trpt p (trpt (inv p) u)) u.
Proof.
  refine (conc _ (_ : Path@{j} (trpt (conc (inv p) p) u) _)).
  -
    exact (inv (trpt_cpq_u P (inv p) p u)).
  -
  refine (conc _ (_ : Path@{j} (trpt idpath u) _)).
  +
    exact (ap (fun p => trpt p u) (conc_vp_p p)).
  +
  simpl trpt.
  exact idpath.
Defined.

(** trpt_inv_p_trpt_p_u です。 *)
Definition trpt_vp_trpt_p_u@{i j | }
  {A : Type@{i}} (P : A -> Type@{j}) {x y : A}
  (p : Path@{i} x y) (u : P x)
  : Path@{j} (trpt (inv p) (trpt p u)) u.
Proof.
  refine (conc _ (_ : Path@{j} (trpt (conc p (inv p)) u) _)).
  -
    exact (inv (trpt_cpq_u P p (inv p) u)).
  -
  refine (conc _ (_ : Path@{j} (trpt idpath u) _)).
  +
    exact (ap (fun p => trpt p u) (conc_p_vp p)).
  +
  simpl trpt.
  exact idpath.
Defined.

Section trpt_conc_p_conc_q_r_u_P_L_R.
  Universe i j.

  Context {A : Type@{i}}.
  Context (P : A -> Type@{j}).
  Context {x y z w : A}.
  Context (p : Path@{i} x y).
  Context (q : Path@{i} y z).
  Context (r : Path@{i} z w).
  Context (u : P x).

  (** trpt_conc_p_conc_q_r_u です。 *)
  Definition trpt_conc_p_conc_q_r_u_L
    : Path@{j} (trpt (conc p (conc q r)) u) (trpt r (trpt q (trpt p u))).
  Proof.
    refine (conc _ (_ : Path@{j} (trpt r (trpt (conc p q) u)) _)).
    -
      refine (conc _ (_ : Path@{j} (trpt (conc (conc p q) r) u) _)).
      +
        exact (ap (fun s => trpt s u) (conc_p_cqr p q r)).
      +
        exact (trpt_cpq_u P (conc p q) r u).
    -
      exact (ap (trpt r) (trpt_cpq_u P p q u)).
  Defined.

  (** trpt_conc_p_conc_q_r_u です。 *)
  Definition trpt_conc_p_conc_q_r_u_R
    : Path@{j} (trpt (conc p (conc q r)) u) (trpt r (trpt q (trpt p u))).
  Proof.
    refine (conc _ (_ : Path@{j} (trpt (conc q r) (trpt p u)) _)).
    -
      exact (trpt_cpq_u P p (conc q r) u).
    -
      exact (trpt_cpq_u P q r (trpt p u)).
  Defined.

  (** Path_'trpt_conc_p_conc_q_r_u_L'_'trpt_conc_p_conc_q_r_u_R' です。 *)
  Definition trpt_conc_p_conc_q_r_u_P_L_R
    : Path@{j} trpt_conc_p_conc_q_r_u_L trpt_conc_p_conc_q_r_u_R.
  Proof.
    unfold trpt_conc_p_conc_q_r_u_L.
    unfold trpt_conc_p_conc_q_r_u_R.
    refine (match r with idpath => _ end).
    refine (match q with idpath => _ end).
    refine (match p with idpath => _ end).
    simpl conc.
    exact idpath.
  Defined.
End trpt_conc_p_conc_q_r_u_P_L_R.
