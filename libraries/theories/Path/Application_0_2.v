(* Run with -nois. *)
(** [GiC.Path.Application_2_0] は、 [ap02] に関する定理を提供します。 *)

(** 必要なライブラリを要求します。 *)

Require GiC.Base.
Require GiC.Path.Base.
Require GiC.Path.OneDim.
Require GiC.Path.Function.
Require GiC.Path.TwoDim.
Require GiC.Path.Fibration.
Require GiC.Path.Transport.
Require GiC.Path.Transport_2.
Require GiC.Path.Application_D.

(** 必要なモジュールをインポートします。 *)

Import GiC.Base.
Import GiC.Path.Base.
Import GiC.Path.OneDim.
Import GiC.Path.Function.
Import GiC.Path.TwoDim.
Import GiC.Path.Fibration.
Import GiC.Path.Transport.
Import GiC.Path.Transport_2.
Import GiC.Path.Application_D.

(** 帰納原理 (induction principle) を生成しないように設定します。 *)

Unset Elimination Schemes.

(** 宇宙多相 (universe polymorphism) について設定します。 *)

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

(** タクティックが使用できるように設定します。 *)

Set Default Proof Mode "Classic".

(** ビュレットを使用しないときにエラーになるように設定します。 *)

Set Default Goal Selector "!".

(** ** [ap02] に関する定理 *)

(** [ap02 f (conc r r')] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1226 *)
Definition ap02_f_crr'@{i j | }
  {A : Type@{i}} {B : Type@{j}}
  (f : A -> B) {x y : A} {p p' p'' : Path@{i} x y}
  (r : Path@{i} p p') (r' : Path@{i} p' p'')
  : Path@{j} (ap02 f (conc r r')) (conc (ap02 f r) (ap02 f r')).
Proof.
  refine (match r' with idpath => _ end).
  refine (match r with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** [ap02 f (conc2 r s)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1232 *)
Definition ap02_f_conc2_r_s@{i j | }
  {A : Type@{i}} {B : Type@{j}} (f : A -> B)
  {x y z : A} {p p' : Path@{i} x y} {q q' : Path@{i} y z}
  (r : Path@{i} p p') (s : Path@{i} q q')
  : Path@{j}
    (ap02 f (conc2 r s))
    (conc
      (conc
        (ap_f_cpq f p q)
        (conc2 (ap02 f r) (ap02 f s)))
      (inv (ap_f_cpq f p' q'))).
Proof.
  refine (match s with idpath => _ end).
  refine (match r with idpath => _ end).
  refine (match q with idpath => _ end).
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** ** [apD02] に関する定理 *)

(** [apD02 f r] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1245 *)
Definition apD02_f_r@{i j | }
  {A : Type@{i}} {B : Type@{j}} (f : A -> B)
  {x y : A} {p q : Path@{i} x y} (r : Path@{i} p q)
  : Path@{j}
    (apD02 f r)
    (conc
      (conc
        (conc
          (apD_f_p f p)
          (conc2
            (inv
              (conc_trpt2_A_lam_x_B_q_u_'trpt1_A_lam_x_B_p_u'_p'_u
                r
                (f x)))
            (ap02 f r)))
        (inv
          (conc_p_cqr
            (trpt2 A (fun _ : A => B) r (f x))
            (trpt1_A_lam_x_B_p_u q (f x))
            (ap01 f q))))
      (whiskerL (trpt2 A (fun _ : A => B) r (f x)) (inv (apD_f_p f q)))).
Proof.
  refine (match r with idpath => _ end).
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** [apD02 f (conc r0 r1)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1256 *)
Definition apD02_f_cr0r1@{i j | }
  (A : Type@{i}) (B : A -> Type@{j}) (f : forall x : A, B x) {x y : A}
  {p p' p'' : Path@{i} x y} (r0 : Path@{i} p p') (r1 : Path@{i} p' p'')
  : Path@{j}
    (apD02 f (conc r0 r1))
    (conc
      (conc
        (conc
          (apD02 f r0)
          (whiskerL (trpt2 A B r0 (f x)) (apD02 f r1)))
        (conc_p_cqr _ _ _))
      (whiskerR (inv (trpt2_A_B_cq0q1_y B r0 r1 (f x))) (apD f p''))).
Proof.
  refine (match r1 with idpath => _ end).
  refine (match r0 with idpath => _ end).
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** [conc (conc (ap (trpt1 Type@{i} idmap@{si} (inv q)) (ap (fun s => trpt1 Type@{i} idmap@{si} s z) r)) (ap (fun s => trpt1 Type@{i} idmap@{si} s (trpt p z)) (inv2 r))) (trpt_vp_trpt_p_u idmap p z)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1268 *)
Definition conc_conc_ap_trpt1_Type_idmap_inv_q_ap_lam_s_trpt1_Type_idmap_s_z_r_ap_lam_s_trpt1_Type_idmap_s_trpt_p_z_inv2_r_'trpt_vp_trpt_p_u'_idmap_p_z
  @{i si | i < si}
  {A B : Type@{i}} (p q : Path@{si} A B) (r : Path@{si} q p) (z : A)
  : Path@{si}
    (conc
      (conc
        (ap
          (trpt1 Type@{i} idmap@{si} (inv q))
          (ap (fun s => trpt1 Type@{i} idmap@{si} s z) r))
        (ap (fun s => trpt1 Type@{i} idmap@{si} s (trpt p z)) (inv2 r)))
      (trpt_vp_trpt_p_u idmap p z))
    (trpt_vp_trpt_p_u idmap q z).
Proof.
  refine (match r with idpath => _ end).
  refine (match q with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** [conc (conc (ap (trpt1 Type@{i} idmap@{si} q) (ap (fun s => trpt1 Type@{i} idmap@{si} (inv s) z) r)) (ap (fun s => trpt1 Type@{i} idmap@{si} s (trpt (inv p) z)) r)) (trpt_p_trpt_vp_u idmap p z)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L1277 *)
Definition conc_conc_ap_trpt1_Type_idmap_q_ap_lam_s_trpt1_Type_idmap_inv_s_z_r_ap_lam_s_trpt1_Type_idmap_s_trpt_inv_p_z_r_'trpt_p_trpt_vp_u'_idmap_p_z
  @{i si | i < si}
  {A B : Type@{i}} (p q : Path@{si} A B) (r : Path@{si} q p) (z : B)
  : Path@{si}
    (conc
      (conc
        (ap
          (trpt1 Type@{i} idmap@{si} q)
          (ap (fun s => trpt1 Type@{i} idmap@{si} (inv s) z) r))
        (ap (fun s => trpt1 Type@{i} idmap@{si} s (trpt (inv p) z)) r))
      (trpt_p_trpt_vp_u idmap p z))
    (trpt_p_trpt_vp_u idmap q z).
Proof.
  refine (match r with idpath => _ end).
  Fail refine
    (match q
      as q'
      in Path _ B'
      return
        Path@{si}
          (conc
            (conc
              (ap
                (trpt1 Type@{i} idmap@{si} q')
                (ap
                  (fun s : Path@{si} A B' =>
                    trpt1 Type@{i} idmap@{si} (inv s) z)
                  idpath))
              (ap
                (fun s : Path@{si} A B' =>
                  trpt1 Type@{i} idmap@{si} s (trpt (inv q') z)) idpath))
            (trpt_p_trpt_vp_u idmap q' z))
          (trpt_p_trpt_vp_u idmap q' z)
      with idpath => _
    end).
  refine (let t := _ in t z).
  refine (match q with idpath => _ end).
  refine (fun z_ => _).
  cbv.
  exact idpath.
Defined.
