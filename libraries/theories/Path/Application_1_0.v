(* Run with -nois. *)

(** * GiC.Path.Application_1_0 *)

(** [GiC.Path.Application_1_0] は [ap10] に関する定理を提供します。

    具体的には、 [ap10] と [ap10D] に関する定理を定義しています。
 *)

(** 必要なライブラリを要求します。 *)
Require GiC.Base.
Require GiC.Function.
Require GiC.Path.Base.

(** 必要なライブラリをインポートします。 *)
Import GiC.Base.
Import GiC.Function.
Import GiC.Path.Base.

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

(** ap10_idpath_x です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L611 *)
Definition ap10_1_x@{i j mij | i <= mij, j <= mij}
  {A : Type@{i}} {B : Type@{j}} (f : A -> B) (x : A)
  : Path@{j} (ap10 (idpath@{mij} f) x) (idpath (f x)).
Proof.
  simpl ap10.
  exact idpath.
Defined.

(** ap10_conc_p_q_x です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L614 *)
Definition ap10_cpq_x@{i j mij | i <= mij, j <= mij}
  {A : Type@{i}} {B : Type@{j}} {f f' f'' : A -> B}
  (pff' : Path@{mij} f f') (pf'f'' : Path@{mij} f' f'') (x : A)
  : Path@{j}
    (ap10 (conc pff' pf'f'') x)
    (conc (ap10 pff' x) (ap10 pf'f'' x)).
Proof.
  refine (match pf'f'' with idpath => _ end).
  refine (match pff' with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** ap10_inv_p_x です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L618 *)
Definition ap10_vp_x@{i j mij | i <= mij, j <= mij}
  {A : Type@{i}} {B : Type@{j}} {f f' : A -> B}
  (pff' : Path@{mij} f f') (x : A)
  : Path@{j} (ap10 (inv pff') x) (inv (ap10 pff' x)).
Proof.
  refine (match pff' with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** ap10D_idpath_x です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L596 *)
Definition ap10D_1_x@{i j mij | i <= mij, j <= mij}
  {A : Type@{i}} {B : A -> Type@{j}} (f : forall x : A, B x) (x : A)
  : Path@{j} (ap10D (idpath@{mij} f) x) (idpath (f x)).
Proof.
  cbv.
  exact idpath.
Defined.

(** ap10D_conc_p_q_x です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L600 *)
Definition ap10D_cpq_x@{i j mij | i <= mij, j <= mij}
  {A : Type@{i}} {B : A -> Type@{j}} {f f' f'' : forall x : A, B x}
  (pff' : Path@{mij} f f') (pf'f'' : Path@{mij} f' f'') (x : A)
  : Path@{j}
    (ap10D (conc pff' pf'f'') x)
    (conc (ap10D pff' x) (ap10D pf'f'' x)).
Proof.
  refine (match pf'f'' with idpath => _ end).
  refine (match pff' with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** ap10D_inv_p_x です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L607 *)
Definition ap10D_vp_x@{i j mij | i <= mij, j <= mij}
  {A : Type@{i}} {B : A -> Type@{j}} {f f' : forall x : A, B x}
  (pff' : Path@{mij} f f') (x : A)
  : Path@{j} (ap10D (inv pff') x) (inv (ap10D pff' x)).
Proof.
  refine (match pff' with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** ap10_ap_lam_f_compNNN_f_g_p_x です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L629 *)
Definition ap10_ap_lam_f_compNNN_f_g_p_x
  @{i j k mjk mik | j <= mjk, k <= mjk, i <= mik, k <= mik}
  {A : Type@{i}} {B : Type@{j}} {C : Type@{k}} {f f' : B -> C} {g : A -> B}
  (pff' : Path@{mjk} f f') (x : A)
  : Path@{k}
    (ap10@{i k mik} (ap (fun f => compNNN f g) pff') x)
    (ap10@{j k mjk} pff' (g x)).
Proof.
  refine (match pff' with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** ap10D_ap_lam_f_compNND_f_g_p_x です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L623 *)
Definition ap10D_ap_lam_f_compNND_f_g_p_x
  @{i j k mjk mik | j <= mjk, k <= mjk, i <= mik, k <= mik}
  {A : Type@{i}} {B : Type@{j}} {C : B -> Type@{k}}
  {f f' : forall x : B, C x} {g : A -> B}
  (pff' : Path@{mjk} f f') (x : A)
  : Path@{k}
    (ap10D@{i k mik} (ap (fun f => compNND f g) pff') x)
    (ap10D@{j k mjk} pff' (g x)).
Proof.
  refine (match pff' with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** ap10_ap_lam_g_compNNN_f_g_p_x です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L639 *)
Definition ap10_ap_lam_g_compNN_f_g_p_x
  @{i j k mij mik | i <= mij, j <= mij, i <= mik, k <= mik}
  {A : Type@{i}} {B : Type@{j}} {C : Type@{k}} {f : B -> C} {g g' : A -> B}
  (pgg' : Path@{mij} g g') (x : A)
  : Path@{k}
    (ap10@{i k mik} (ap (fun g => compNNN f g) pgg') x)
    (ap f (ap10@{i j mij} pgg' x)).
Proof.
  refine (match pgg' with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** ap10D_ap_lam_g_compNDN_f_g_p_x です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L633 *)
Definition ap10D_ap_lam_g_compND_f_g_p_x
  @{i j k mij mik | i <= mij, j <= mij, i <= mik, k <= mik}
  {A : Type@{i}} {B : A -> Type@{j}} {C : Type@{k}}
  {f : forall x : A, B x -> C} {g g' : forall x : A, B x}
  (pgg' : Path@{mij} g g') (x : A)
  : Path@{k}
    (ap10D@{i k mik} (ap (fun g => compNDN f g) pgg') x)
    (ap (f x) (ap10D@{i j mij} pgg' x)).
Proof.
  refine (match pgg' with idpath => _ end).
  cbv.
  exact idpath.
Defined.
