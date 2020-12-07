(*

Copyright 2020 Hexirp Prixeh

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

*)

(* Run with -nois. *)

(** * GiC.Path.Application_1_1 *)

(** [GiC.Path.Application_1_1] は [ap11] に関する定理を提供します。

    具体的には、 [ap11] に関する定理を定義しています。
 *)

(** 必要なライブラリをインポートします。 *)
Require Import GiC.Base GiC.Path.Base.

(** 帰納原理 (induction principle) を生成しないように設定します。 *)
Unset Elimination Schemes.

(** 宇宙多相 (universe polymorphism) について設定します。 *)
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

(** 宇宙 (universe) について表示するように設定します。 *)
Set Printing Universes.

(** タクティックが使用できるように設定します。 *)
Set Default Proof Mode "Classic".

(** ap11_h_p です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L733 *)
Definition ap11_h_p@{i j mij | i <= mij, j <= mij}
  {A : Type@{i}} {B : Type@{j}}
  {f f' : A -> B} (pff' : Path@{mij} f f')
  {x x' : A} (pxx' : Path@{i} x x')
  : Path@{j} (ap11 pff' pxx') (conc (ap10 pff' x) (ap01 f' pxx')).
Proof.
  refine (match pxx' with idpath => _ end).
  refine (match pff' with idpath => _ end).
  cbv.
  exact idpath.
Defined.
