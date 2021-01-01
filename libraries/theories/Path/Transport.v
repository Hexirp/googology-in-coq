(* Run with -nois. *)

(** * GiC.Path.Transport *)

(** [GiC.Path.Transport] は、亜群構造の上での道による輸送に関する定理を提供します。

    具体的には、 [trpt] に関する基本的な定理や、高度な一貫性 (coherence) に関する定理、依存型を対象とする [trpt] の変種に関する定理などを含みます。
 *)

(** 必要なライブラリを要求します。 *)
Require GiC.Base.
Require GiC.Path.Base.
Require GiC.Path.Function.
Require GiC.Path.OneDim.
Require GiC.Path.Transposition.

(** 必要なライブラリをインポートします。 *)
Import GiC.Base.
Import GiC.Path.Base.
Import GiC.Path.Function.
Import GiC.Path.OneDim.
Import GiC.Path.Transposition.

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

(** ** 道による輸送の基本的な定理 *)

(** [trpt idpath u] です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L645 *)
Definition trpt_1_u@{i j | }
  {A : Type@{i}} (P : A -> Type@{j}) {x : A} (u : P x)
  : Path@{j} (trpt idpath u) u.
Proof.
  cbv.
  exact idpath.
Defined.

(** [trpt (conc p q) u] です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L649 *)
Definition trpt_cpq_u@{i j | }
  {A : Type@{i}} (P : A -> Type@{j}) {x y z : A}
  (p : Path@{i} x y) (q : Path@{i} y z) (u : P x)
  : Path@{j} (trpt (conc p q) u) (trpt q (trpt p u)).
Proof.
  refine (match q with idpath => _ end).
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** [trpt p (trpt (inv p) u)] です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L655 *)
Definition trpt_p_trpt_vp_u@{i j | }
  {A : Type@{i}} (P : A -> Type@{j}) {x y : A}
  (p : Path@{i} x y) (u : P y)
  : Path@{j} (trpt p (trpt (inv p) u)) u.
Proof.
  refine_conc (trpt (conc (inv p) p) u).
  -
    exact (inv (trpt_cpq_u P (inv p) p u)).
  -
  refine_conc (trpt idpath u).
  +
    exact (ap (fun p => trpt p u) (conc_vp_p p)).
  +
  cbv.
  exact idpath.
Defined.

(** [trpt (inv p) (trpt p u)] です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L660 *)
Definition trpt_vp_trpt_p_u@{i j | }
  {A : Type@{i}} (P : A -> Type@{j}) {x y : A}
  (p : Path@{i} x y) (u : P x)
  : Path@{j} (trpt (inv p) (trpt p u)) u.
Proof.
  refine_conc (trpt (conc p (inv p)) u).
  -
    exact (inv (trpt_cpq_u P p (inv p) u)).
  -
  refine_conc (trpt idpath u).
  +
    exact (ap (fun p => trpt p u) (conc_p_vp p)).
  +
  cbv.
  exact idpath.
Defined.

(** ** 輸送についての一貫性 (coherence) に関する補題 *)

(** [trpt_conc_p_conc_q_r_u_Path_L_R] を定義するためのセクションです。 *)
Section trpt_conc_p_conc_q_r_u_Path_L_R.
  Universe i j.

  Context {A : Type@{i}}.
  Context (P : A -> Type@{j}).
  Context {x y z w : A}.
  Context (p : Path@{i} x y).
  Context (q : Path@{i} y z).
  Context (r : Path@{i} z w).
  Context (u : P x).

  (** [trpt (conc p (conc q r)) u] です。 *)
  (* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L667 *)
  Definition trpt_conc_p_conc_q_r_u_L
    : Path@{j} (trpt (conc p (conc q r)) u) (trpt r (trpt q (trpt p u))).
  Proof.
    refine_conc (trpt r (trpt (conc p q) u)).
    -
      refine_conc (trpt (conc (conc p q) r) u).
      +
        exact (ap (fun s => trpt s u) (conc_p_cqr p q r)).
      +
        exact (trpt_cpq_u P (conc p q) r u).
    -
      exact (ap (trpt r) (trpt_cpq_u P p q u)).
  Defined.

  (** [trpt (conc p (conc q r)) u] です。 *)
  (* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L667 *)
  Definition trpt_conc_p_conc_q_r_u_R
    : Path@{j} (trpt (conc p (conc q r)) u) (trpt r (trpt q (trpt p u))).
  Proof.
    refine_conc (trpt (conc q r) (trpt p u)).
    -
      exact (trpt_cpq_u P p (conc q r) u).
    -
      exact (trpt_cpq_u P q r (trpt p u)).
  Defined.

  (** [Path trpt_conc_p_conc_q_r_u_L trpt_conc_p_conc_q_r_u_R] です。 *)
  (* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L667 *)
  Definition trpt_conc_p_conc_q_r_u_Path_L_R
    : Path@{j} trpt_conc_p_conc_q_r_u_L trpt_conc_p_conc_q_r_u_R.
  Proof.
    unfold trpt_conc_p_conc_q_r_u_L.
    unfold trpt_conc_p_conc_q_r_u_R.
    refine (match r with idpath => _ end).
    refine (match q with idpath => _ end).
    refine (match p with idpath => _ end).
    cbv.
    exact idpath.
  Defined.
End trpt_conc_p_conc_q_r_u_Path_L_R.

(** [trpt_p_trpt_vp_u P p (trpt p u)] です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L679 *)
Definition _'trpt_p_trpt_vp_u'_P_p_trpt_p_u@{i j | }
  {A : Type@{i}} (P : A -> Type@{j}) {x y : A}
  (p : Path@{i} x y) (u : P x)
  : Path@{j}
    (trpt_p_trpt_vp_u P p (trpt p u))
    (ap (trpt p) (trpt_vp_trpt_p_u P p u)).
Proof.
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** [trpt_vp_trpt_p_u P p (trpt (inv p) u)] です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L679 *)
Definition _'trpt_vp_trpt_p_u'_P_p_trpt_vp_u@{i j | }
  {A : Type@{i}} (P : A -> Type@{j}) {x y : A}
  (p : Path@{i} x y) (u : P y)
  : Path@{j}
    (trpt_vp_trpt_p_u P p (trpt (inv p) u))
    (ap (trpt (inv p)) (trpt_p_trpt_vp_u P p u)).
Proof.
  refine (let t := _ in t u).
  refine (match p
    as p'
    in Path _ y'
    return forall u' : P y',
      Path@{j}
        (trpt_vp_trpt_p_u P p' (trpt (inv p') u'))
        (ap (trpt (inv p')) (trpt_p_trpt_vp_u P p' u'))
    with idpath => _
  end).

  move=> u'.
  cbv.
  exact idpath.
Defined.

(** [conc (ap (trpt p) (path_u_trpt_vp_v P p u v e)) (trpt_p_trpt_vp_u P p v)] です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L693 *)
Definition conc_ap_trpt_p_'path_u_trpt_vp_v'_P_p_u_v_e_'trpt_p_trpt_vp_u'_P_p_v
  @{i j | }
  {A : Type@{i}} (P : A -> Type@{j}) {x y : A}
  (p : Path@{i} x y) (u : P x) (v : P y) (e : Path@{j} (trpt p u) v)
  : Path@{j}
    (conc
      (ap (trpt p) (fun_Path_trpt_p_u_v_Path_u_trpt_vp_v P p u v e))
      (trpt_p_trpt_vp_u P p v))
    e.
Proof.
  refine (match e with idpath => _ end).
  refine (match p with idpath => _ end).
  cbv.
  refine idpath.
Defined.

(** [path_u_trpt_vp_v P p u (trpt p u) idpath] です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L701 *)
Definition _'path_u_trpt_vp_v'_P_p_u_trpt_p_u_1@{i j | }
  {A : Type@{i}} (P : A -> Type@{j}) {x y : A}
  (p : Path@{i} x y) (u : P x)
  : Path@{j}
    (fun_Path_trpt_p_u_v_Path_u_trpt_vp_v P p u (trpt p u) idpath)
    (inv (trpt_vp_trpt_p_u P p u)).
Proof.
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** ** 依存型を対象とした変種についての定理 *)

(** [f x' (trptD A_ B0 p y)] です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L817 *)
Definition f_x'_trptD_A_B0_p_y@{i j0 j1 | }
  (A : Type@{i}) (B0 : A -> Type@{j0}) (B1 : A -> Type@{j1})
  (f : forall a : A, B0 a -> B1 a) {x x' : A} (p : Path@{i} x x') (y : B0 x)
  : Path@{j1} (f x' (trptD A B0 p y)) (trptD A B1 p (f x y)).
Proof.
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** [f x' (trptD A B p y) (trptDD A B C0 p y z)] です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L823 *)
Definition f_x'_trptD_A_B_p_y_trptDD_A_B_C0_p_y_z@{i j k0 k1 | }
  (A : Type@{i}) (B : A -> Type@{j})
  (C0 : forall a : A, B a -> Type@{k0}) (C1 : forall a : A, B a -> Type@{k1})
  (f : forall (a : A) (b : B a), C0 a b -> C1 a b)
  {x x' : A} (p : Path@{i} x x') (y : B x) (z : C0 x y)
  : Path@{k1}
    (f x' (trptD A B p y) (trptDD A B C0 p y z))
    (trptDD A B C1 p y (f x y z)).
Proof.
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** [f x' (trptD A B0 p y0) (trptD A B1 p y1) (trpt_N_D_D_DD A B0 B1 C0 p y0 y1 z)] です。 *)
(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L833 *)
Definition f_x'_T_T_'trpt_N_D_D_DD'_A_B0_B1_C0_p_y0_y1_z@{i j0 j1 k0 k1 | }
  (A : Type@{i}) (B0 : A -> Type@{j0}) (B1 : A -> Type@{j1})
  (C0 : forall a : A, B0 a -> B1 a -> Type@{k0})
  (C1 : forall a : A, B0 a -> B1 a -> Type@{k1})
  (f : forall (a : A) (b0 : B0 a) (b1 : B1 a), C0 a b0 b1 -> C1 a b0 b1)
  {x x' : A} (p : Path@{i} x x') (y0 : B0 x) (y1 : B1 x) (z : C0 x y0 y1)
  : Path@{k1}
    (f
      x'
      (trptD A B0 p y0)
      (trptD A B1 p y1)
      (trpt_N_D_D_DD A B0 B1 C0 p y0 y1 z))
    (trpt_N_D_D_DD A B0 B1 C1 p y0 y1 (f x y0 y1 z)).
Proof.
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** ** [ap] が絡んだ補題 *)

(** [ap (trpt p) (ap (trpt (inv p)) q)] です。 *)
(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L844 *)
Definition ap_trpt_p_ap_trpt_vp_q@{i j | }
  (A : Type@{i}) (P : A -> Type@{j})
  {x x' : A} (p : Path@{i} x x') {y y' : P x'} (q : Path@{j} y y')
  : Path@{j}
    (ap (trpt p) (ap (trpt (inv p)) q))
    (conc (conc (trpt_p_trpt_vp_u P p y) q) (inv (trpt_p_trpt_vp_u P p y'))).
Proof.
  refine (match q with idpath => _ end).

  refine (let t := _ in t y).
  refine (match p
    as p_
    in Path _ x'_
    return
      forall y_ : P x'_,
        Path@{j}
          (ap (trpt p_) (ap (trpt (inv p_)) idpath))
          (conc
            (conc (trpt_p_trpt_vp_u P p_ y_) idpath)
            (inv (trpt_p_trpt_vp_u P p_ y_)))
    with idpath => _
  end).

  move=> y_.
  cbv.
  exact idpath.
Defined.

(** [conc (ap (trpt p) (apD f (inv p))) (apD f p)] です。 *)
(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L853 *)
Definition conc_ap_trpt_p_apD_f_vp_apD_f_p@{i j | }
  {A : Type@{i}} (P : A -> Type@{j}) (f : forall x : A, P x)
  {x x' : A} (p : Path@{i} x x')
  : Path@{j}
    (conc (ap (trpt p) (apD f (inv p))) (apD f p))
    (trpt_p_trpt_vp_u P p (f x')).
Proof.
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.
