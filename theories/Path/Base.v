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

(** * GiC.Path.Base *)

(** [GiC.Path.Base] は道に関する基本的な定義を提供します。

    具体的には、よく現れるパターンを一般化したタクティックや、 [GiC.Base] にある関数の単純なバリエーションなどを定義します。
 *)

(** 必要なライブラリをインポートします。 *)
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

(** ** 汎用的なタクティックの定義 *)

(** [refine_conc t] は [Path x y -| Path x t, Path t y] です。 *)
Ltac refine_conc t := refine (@GiC.Base.conc@{_} _ _ t _ _ _).

(** ** 汎用的な関数の定義 *)

(** 一変数関数に対する ap です。 *)
(* from: originally defined by Hexirp *)
Definition ap1@{i j | }
  {A : Type@{i}} {B : Type@{j}} (f : A -> B) {x x' : A} (p : Path@{i} x x')
  : Path@{j} (f x) (f x')
  := ap f p.

(** 二変数関数に対する ap です。 *)
(* from: originally defined by Hexirp *)
Definition ap2@{i j k | }
  {A : Type@{i}} {B : Type@{j}} {C : Type@{k}} (f : A -> B -> C)
  {x x' : A} (p : Path@{i} x x') {y y' : B} (q : Path@{j} y y')
  : Path@{k} (f x y) (f x' y')
  := match p with idpath => ap1 (f x) q end.

(** 三変数関数に対する ap です。 *)
(* from: originally defined by Hexirp *)
Definition ap3@{i j k l | }
  {A : Type@{i}} {B : Type@{j}} {C : Type@{k}} {D : Type@{l}}
  (f : A -> B -> C -> D)
  {x x' : A} (p : Path@{i} x x')
  {y y' : B} (q : Path@{j} y y')
  {z z' : C} (r : Path@{k} z z')
  : Path@{l} (f x y z) (f x' y' z')
  := match p with idpath => ap2 (f x) q r end.

(** 依存型に対応する ap です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/Overture.v#L439 *)
Definition apD@{i j | }
  {A : Type@{i}} {B : A -> Type@{j}} (f : forall x : A, B x)
  {x y : A} (p : Path@{i} x y)
  : Path@{j} (trpt p (f x)) (f y)
  := match p with idpath => idpath end.

(** 関数の 0-道を値の 0-道に適用する関数です。 *)
(* from: originally defined by Hexirp *)
Definition ap00@{i j | } {A : Type@{i}} {B : Type@{j}}
  (f : A -> B) (x : A) : B
  := apply f x.

(** 関数の 0-道を値の 1-道に適用する関数です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/Overture.v#L374 *)
Definition ap01@{i j | } {A : Type@{i}} {B : Type@{j}}
  (f : A -> B) {x x' : A} (pxx' : Path@{i} x x') : Path@{j} (f x) (f x')
  := ap f pxx'.

(** 関数の 1-道を値の 0-道に適用する関数です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/Overture.v#L417 *)
Definition ap10@{i j mij | i <= mij, j <= mij} {A : Type@{i}} {B : Type@{j}}
  {f f' : A -> B} (pff' : Path@{mij} f f') (x : A) : Path@{j} (f x) (f' x)
  := match pff' with idpath => idpath end.

(** 依存関数の 1-道を値の 0-道に適用する関数です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/Overture.v#L411 *)
Definition ap10D@{i j mij | i <= mij, j <= mij}
  {A : Type@{i}} {B : A -> Type@{j}}
  {f f' : forall a : A, B a} (pff' : Path@{mij} f f') (x : A)
  : Path@{j} (f x) (f' x)
  := match pff' with idpath => idpath end.

(** 関数の 1-道を値の 1-道に適用する関数です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/Overture.v#L425 *)
Definition ap11@{i j mij | i <= mij, j <= mij} {A : Type@{i}} {B : Type@{j}}
  {f f' : A -> B} (pff' : Path@{mij} f f') {x x' : A} (pxx' : Path@{i} x x')
  : Path@{j} (f x) (f' x')
  := match pxx' with idpath => match pff' with idpath => idpath end end.

(** 二変数関数の 0-道を値の 1-道と 1-道に適用する関数です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L755 *)
Definition ap011@{i j k | }
  {A : Type@{i}} {B : Type@{j}} {C : Type@{k}}
  (f : A -> B -> C)
  {x x' : A} (pxx' : Path@{i} x x')
  {y y' : B} (pyy' : Path@{j} y y')
  : Path@{k} (f x y) (f x' y')
  := match pyy' with idpath => match pxx' with idpath => idpath end end.
