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

(** * GiC.Path.Function *)

(** [GiC.Path.Function] は道に関する関数を提供します。

    具体的には、 [GiC.Base] にある道の関数のバリエーションを提供します。それには [GiC.Path.Base] よりも複雑な関数を含みます。
 *)

(** 必要なライブラリをインポートします。 *)
Require Import GiC.Base GiC.Function GiC.Path.Base.

(** 帰納原理 (induction principle) を生成しないように設定します。 *)
Unset Elimination Schemes.

(** 宇宙多相 (universe polymorphism) について設定します。 *)
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

(** 宇宙 (universe) について表示するように設定します。 *)
Set Printing Universes.

(** タクティックが使用できるように設定します。 *)
Set Default Proof Mode "Classic".

(** ** [trpt] の変種 *)

(** [A] の道で、一重の依存型 [B x] を輸送する [trpt] です。 *)
(* from: originally defined by Hexirp *)
Definition trptD@{i j | }
  (A : Type@{i}) (B : A -> Type@{j})
  {x x' : A} (p : Path@{i} x x') (y : B x)
  : B x'
  := trpt p y.

(** [A] の道で、一重の依存型 [B x] と、二重の依存型 [C x y] を輸送する [trpt] です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L741 *)
Definition trptDD@{i j k | }
  (A : Type@{i}) (B : A -> Type@{j}) (C : forall a : A, B a -> Type@{k})
  {x x' : A} (p : Path@{i} x x') (y : B x) (z : C x y)
  : C x' (trptD A B p y)
  := match p with idpath => z end.

(** [A] の道で、一重の依存型 [B x] と、二重の依存型 [C x y] と、三重の依存型 [D x y z] を輸送する [trpt] です。 *)
(* from: originally defined by Hexirp *)
Definition trptDDD@{i j k l | }
  (A : Type@{i}) (B : A -> Type@{j})
  (C : forall a : A, B a -> Type@{k})
  (D : forall (a : A) (b : B a), C a b -> Type@{l})
  {x x' : A} (p : Path@{i} x x') (y : B x) (z : C x y) (w : D x y z)
  : D x' (trptD A B p y) (trptDD A B C p y z)
  := match p with idpath => w end.

(** [A] の道で、一重の依存型 [B x] を輸送する [trpt] です。 *)
(* from: originally defined by Hexirp *)
Definition trpt_N_D@{i j | }
  (A : Type@{i}) (B : A -> Type@{j})
  {x x' : A} (p : Path@{i} x x') (y : B x)
  : B x'
  := trptD A B p y.

(** [A] の道で、一重の依存型 [B x] と、二重の依存型 [C x y] を輸送する [trpt] です。 *)
(* from: originally defined by Hexirp *)
Definition trpt_N_D_DD@{i j k | }
  {A : Type@{i}} {B : A -> Type@{j}} {C : forall a : A, B a -> Type@{k}}
  {x x' : A} (p : Path@{i} x x') (y : B x) (z : C x y)
  : C x' (trptD A B p y)
  := trptDD A B C p y z.

(** [A] の道で、一重の依存型 [B0 x] と、一重の依存型 [B0 x] と、二重の依存型 [C x y0 y1] を輸送する [trpt] です。 *)
(* i j k l や A B C D という風に連番として書かない理由は、 trptN, trptD, trptDD, ... という系列の型を表記する際に連番が既に使われているからです。 *)
(* j と j' や B と B' という風にアポストロフィを加えて書かない理由は、 x と x' をという風に書く時は x と x' の間に道があるということを暗示しているため、この場合は使えないからです。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L747 *)
Definition trpt_N_D_D_DD@{i j0 j1 k | }
  {A : Type@{i}} {B0 : A -> Type@{j0}} {B1 : A -> Type@{j1}}
  {C : forall a : A, B0 a -> B1 a -> Type@{k}}
  {x x' : A} (p : Path@{i} x x') (y0 : B0 x) (y1 : B1 x) (z : C x y0 y1)
  : C x' (trptD A B0 p y0) (trptD A B1 p y1)
  := match p with idpath => z end.

(** [A] の 1-道で、依存型 [B x] を輸送する [trpt] です。 *)
(* from: originally defined by Hexirp *)
Definition trpt1@{i j | }
  (A : Type@{i}) (B : A -> Type@{j})
  {x x' : A} (p : Path@{i} x x') (y : B x)
  : B x'
  := trpt p y.

(** [A] の 2-道で、依存型 [B x] を輸送する [trpt] です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L787 *)
Definition trpt2@{i j | }
  (A : Type@{i}) (B : A -> Type@{j})
  {x x' : A} {p p' : Path@{i} x x'} (q : Path@{i} p p')
  (y : B x)
  : Path@{j} (trpt1 A B p y) (trpt1 A B p' y)
  := ap (fun p => trpt1 A B p y) q.

(** [A] の 3-道で、依存型 [B x] を輸送する [trpt] です。 *)
(* from: originally defined by Hexirp *)
Definition trpt3@{i j | }
  (A : Type@{i}) (B : A -> Type@{j})
  {x x' : A} {p p' : Path@{i} x x'} {q q' : Path@{i} p p'} (r : Path@{i} q q')
  (y : B x)
  : Path@{j} (trpt2 A B q y) (trpt2 A B q' y)
  := ap (fun p => trpt2 A B p y) r.

(** ** [ap] の変種 *)

(** 非依存型 [A] から非依存型 [B] への関数の 0-道を、非依存型 [A] の値の 0-道に適用する関数です。 *)
(* from: originally defined by Hexirp *)
Definition ap00_AN_BN@{i j | } {A : Type@{i}} {B : Type@{j}}
  (f : A -> B) (x : A) : B
  := ap00 f x.

(** 非依存型 [A] から依存型 [B a] への関数の 0-道を、非依存型 [A] の値の 0-道に適用する関数です。 *)
(* from: originally defined by Hexirp *)
Definition ap00_AN_BDA@{i j | } {A : Type@{i}} {B : A -> Type@{j}}
  (f : forall x : A, B x) (x : A) : B x
  := applyD f x.

(** 非依存型 [A] から非依存型 [B] への関数の 1-道を、非依存型 [A] の値の 0-道に適用する関数です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/Overture.v#L417 *)
Definition ap10_AN_BN@{i j mij | i <= mij, j <= mij} {A : Type@{i}} {B : Type@{j}}
  {f f' : A -> B} (pff' : Path@{mij} f f') (x : A) : Path@{j} (f x) (f' x)
  := ap10 pff' x.

(** 非依存型 [A] から依存型 [B a] への関数の 1-道を、非依存型 [A] の値の 0-道に適用する関数です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/Overture.v#L411 *)
Definition ap10_AN_BDA@{i j mij | i <= mij, j <= mij}
  {A : Type@{i}} {B : A -> Type@{j}}
  {f f' : forall a : A, B a} (pff' : Path@{mij} f f') (x : A)
  : Path@{j} (f x) (f' x)
  := ap10D pff' x.

(** 非依存型 [A] と非依存型 [B] から非依存型 [C] への関数の 0-道を、非依存型 [A] の値の 1-道と非依存型 [B] の値の 1-道に適用する関数です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L755 *)
Definition ap011_AN_BN_CN@{i j k | }
  {A : Type@{i}} {B : Type@{j}} {C : Type@{k}}
  (f : A -> B -> C)
  {x x' : A} (pxx' : Path@{i} x x')
  {y y' : B} (pyy' : Path@{j} y y')
  : Path@{k} (f x y) (f x' y')
  := match pyy' with idpath => match pxx' with idpath => idpath end end.

(** 非依存型 [A] と依存型 [B a] から非依存型 [C] への関数の 0-道を、非依存型 [A] の値の 1-道と依存型 [B a] の値の 1-道に適用する関数です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L764 *)
Definition ap011_AN_BDA_CN@{i j k | }
  {A : Type@{i}} {B : A -> Type@{j}} {C : Type@{k}}
  (f : forall a : A, B a -> C)
  {x x' : A} (pxx' : Path@{i} x x')
  {y : B x} {y' : B x'} (pyy' : Path@{j} (trpt pxx' y) y')
  : Path@{k} (f x y) (f x' y')
  := match pyy' with idpath => match pxx' with idpath => idpath end end.

(** 非依存型 [A] と依存型 [B a] から依存型 [C a] への関数の 0-道を、非依存型 [A] の値の 1-道と依存型 [B a] の値の 1-道に適用する関数です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L771 *)
Definition ap011_AN_BDA_CDA@{i j k | }
  {A : Type@{i}} {B : A -> Type@{j}} {C : A -> Type@{k}}
  (f : forall a : A, B a -> C a)
  {x x' : A} (pxx' : Path@{i} x x')
  {y : B x} {y' : B x'} (pyy' : Path@{j} (trpt pxx' y) y')
  : Path@{k} (trptD A C pxx' (f x y)) (f x' y')
  := match pyy' with idpath => match pxx' with idpath => idpath end end.

(** 非依存型 [A] と依存型 [B a] から依存型 [C a b] への関数の 0-道を、非依存型 [A] の値の 1-道と依存型 [B a] の値の 1-道に適用する関数です。 *)
(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L778 *)
Definition ap011_AN_BDA_CDAB@{i j k | }
  {A : Type@{i}} {B : A -> Type@{j}} {C : forall a : A, B a -> Type@{k}}
  (f : forall (a : A) (b : B a), C a b)
  {x x' : A} (pxx' : Path@{i} x x')
  {y : B x} {y' : B x'} (pyy' : Path@{j} (trpt pxx' y) y')
  : Path@{k} (trptD (B x') (C x') pyy' (trptDD A B C pxx' y (f x y))) (f x' y')
  := match pyy' with idpath => match pxx' with idpath => idpath end end.
