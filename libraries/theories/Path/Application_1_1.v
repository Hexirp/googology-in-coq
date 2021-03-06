(* Run with -nois. *)
(** [GiC.Path.Application_1_1] は [ap11] に関する定理を提供します。

    具体的には、 [ap11] に関する定理を定義しています。
 *)

(** 必要なライブラリを要求します。 *)

Require GiC.Base.
Require GiC.Path.Base.

(** 必要なモジュールをインポートします。 *)

Import GiC.Base.
Import GiC.Path.Base.

(** 帰納原理 (induction principle) を生成しないように設定します。 *)

Unset Elimination Schemes.

(** 宇宙多相 (universe polymorphism) について設定します。 *)

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

(** タクティックが使用できるように設定します。 *)

Set Default Proof Mode "Classic".

(** ビュレットを使用しないときにエラーになるように設定します。 *)

Set Default Goal Selector "!".

(** [ap11 h p] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L733 *)
Definition ap11_h_p@{i j mij | i <= mij, j <= mij}
  {A : Type@{i}} {B : Type@{j}}
  {f f' : A -> B} (pff' : Path@{mij} f f')
  {x x' : A} (pxx' : Path@{i} x x')
  : Path@{j} (ap11 pff' pxx') (conc (ap10 pff' x) (ap01 f' pxx')).
Proof.
  path_elim pxx'.
  path_elim pff'.
  cbv.
  exact idpath.
Defined.
