(* Run with -nois. *)

(** * GiC.Path.Transport_2 *)

(** [GiC.Path.Transport_2] は、 [trpt2] に関する定理を提供します。 *)

(** 必要なライブラリを要求します。 *)
Require GiC.Base.
Require GiC.Path.Base.
Require GiC.Path.Function.
Require GiC.Path.OneDim.

(** 必要なライブラリをインポートします。 *)
Import GiC.Base.
Import GiC.Path.Base.
Import GiC.Path.Function.
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
