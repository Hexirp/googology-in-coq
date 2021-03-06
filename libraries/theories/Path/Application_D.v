(* Run with -nois. *)
(** [GiC.Path.Application_D] は、 [apD] に関する定理を提供します。

    具体的には、 [GiC.Path.Functoriality] にある定理の [apD] 版などを定義しています。 *)

(** 必要なライブラリを要求します。 *)

Require GiC.Base.
Require GiC.Path.Base.
Require GiC.Path.Transposition.
Require GiC.Path.Transport.
Require GiC.Path.Fibration.

(** 必要なモジュールをインポートします。 *)

Import GiC.Base.
Import GiC.Path.Base.
Import GiC.Path.Transposition.
Import GiC.Path.Transport.
Import GiC.Path.Fibration.

(** 帰納原理 (induction principle) を生成しないように設定します。 *)

Unset Elimination Schemes.

(** 宇宙多相 (universe polymorphism) について設定します。 *)

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

(** タクティックが使用できるように設定します。 *)

Set Default Proof Mode "Classic".

(** ビュレットを使用しないときにエラーになるように設定します。 *)

Set Default Goal Selector "!".

(** ** 道にフォーカスした定理 *)

(** [apD f idpath] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L372 *)
Definition apD_f_1@{i j | }
  {A : Type@{i}} {B : A -> Type@{j}} (f : forall x : A, B x) (x : A)
  : Path@{j} (apD f (idpath x)) (idpath (f x)).
Proof.
  cbv.
  exact idpath.
Defined.

(** [apD f (conc p q)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L860 *)
Definition apD_f_cpq@{i j | }
  {A : Type@{i}} {B : A -> Type@{j}} (f : forall x : A, B x)
  {x y z : A} (p : Path@{i} x y) (q : Path@{i} y z)
  : Path@{j}
    (apD f (conc p q))
    (conc (conc (trpt_cpq_u B p q (f x)) (ap (trpt q) (apD f p))) (apD f q)).
Proof.
  path_elim q.
  path_elim p.
  cbv.
  exact idpath.
Defined.

(** [apD f (inv p)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L868 *)
Definition apD_f_vp@{i j | }
  {A : Type@{i}} {B : A -> Type@{j}} (f : forall x : A, B x)
  {x y : A} (p : Path@{i} x y)
  : Path@{j}
    (apD f (inv p))
    (fun_Path_u_trpt_p_v_Path_trpt_vp_u_v B p (f y) (f x) (inv (apD f p))).
Proof.
  path_elim p.
  cbv.
  exact idpath.
Defined.

(** ** 関数にフォーカスした定理 *)

(** [apD f p] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L953 *)
Definition apD_f_p@{i j | }
  {A : Type@{i}} {B : Type@{j}} (f : A -> B) {x y : A} (p : Path@{i} x y)
  : Path@{j} (apD f p) (conc (trpt1_A_lam_x_B_p_u p (f x)) (ap f p)).
Proof.
  path_elim p.
  cbv.
  exact idpath.
Defined.

(** [apD (comp f g) p] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L959 *)
Definition apD_comp_f_g_p@{i0 i1 j | }
  (A0 : Type@{i0}) (A1 : Type@{i1}) (B : A1 -> Type@{j})
  (f : forall x : A1, B x) (g : A0 -> A1) {x x' : A0} (p : Path@{i0} x x')
  : Path@{j}
    (apD (fun x_ : A0 => f (g x_)) p)
    (conc (trpt1_A0_lam_x_B_f_x_p_y A0 A1 B g p (f (g x))) (apD f (ap g p))).
Proof.
  path_elim p.
  cbv.
  exact idpath.
Defined.

(** [apD f (ap g p)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L966 *)
Definition apD_f_ap_g_p@{i0 i1 j | }
  (A0 : Type@{i0}) (A1 : Type@{i1}) (B : A1 -> Type@{j})
  (f : forall x : A1, B x) (g : A0 -> A1) {x x' : A0} (p : Path@{i0} x x')
  : Path@{j}
    (apD f (ap g p))
    (conc
      (inv (trpt1_A0_lam_x_B_f_x_p_y A0 A1 B g p (f (g x))))
      (apD (fun x_ : A0 => f (g x_)) p)).
Proof.
  path_elim p.
  cbv.
  exact idpath.
Defined.
