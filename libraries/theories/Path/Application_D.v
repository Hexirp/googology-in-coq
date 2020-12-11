(* Run with -nois. *)

(** * GiC.Path.Application_D *)

(** [apD] に関する定理を提供します。

    具体的には、 [GiC.Path.Functoriality] にある定理の [apD] 版などを定義しています。 *)

(** 必要なライブラリをインポートします。 *)
Require Import GiC.Base.
Require Import GiC.Path.Base.
Require Import GiC.Path.Transposition.
Require Import GiC.Path.Transport.

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

(** ** 道の方を扱う定理 *)

(** apD_f_idpath です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L372 *)
Definition apD_f_1@{i j | }
  {A : Type@{i}} {B : A -> Type@{j}} (f : forall x : A, B x) (x : A)
  : Path@{j} (apD f (idpath x)) (idpath (f x)).
Proof.
  cbv.
  exact idpath.
Defined.

(** apD_f_conc_p_q です。 *)
(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L860 *)
Definition apD_f_cpq@{i j | }
  {A : Type@{i}} {B : A -> Type@{j}} (f : forall x : A, B x)
  {x y z : A} (p : Path@{i} x y) (q : Path@{i} y z)
  : Path@{j}
    (apD f (conc p q))
    (conc (conc (trpt_cpq_u B p q (f x)) (ap (trpt q) (apD f p))) (apD f q)).
Proof.
  refine (match q with idpath => _ end).
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** apD_f_inv_p です。 *)
(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L868 *)
Definition apD_f_vp@{i j | }
  {A : Type@{i}} {B : A -> Type@{j}} (f : forall x : A, B x)
  {x y : A} (p : Path@{i} x y)
  : Path@{j}
    (apD f (inv p))
    (path_trpt_vp_u_v B p (f y) (f x) (inv (apD f p))).
Proof.
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.
