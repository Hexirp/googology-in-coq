(* Run with -nois. *)
(** [GiC.Path.Application_2_0] は、 [ap02] に関する定理を提供します。 *)

(** 必要なライブラリを要求します。 *)

Require GiC.Base.
Require GiC.Path.Base.
Require GiC.Path.Function.

(** 必要なモジュールをインポートします。 *)

Import GiC.Base.
Import GiC.Path.Base.
Import GiC.Path.Function.

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
