(* Run with -nois. *)
(** [GiC.Path.Base] は道に関する基本的な定義を提供します。

    具体的には、よく現れるパターンを一般化したタクティックや、 [GiC.Base] にある関数の単純なバリエーションなどを定義します。
 *)

(** 必要なライブラリを要求します。 *)

Require GiC.Base.

(** 必要なモジュールをインポートします。 *)

Import GiC.Base.

(** 帰納原理 (induction principle) を生成しないように設定します。 *)

Unset Elimination Schemes.

(** 宇宙多相 (universe polymorphism) について設定します。 *)

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

(** ** 汎用的なタクティックの定義 *)

(** [refine_conc t] は [Path x z] というゴールを [Path x t] と [Path t z] へ分解します。 *)

Ltac refine_by_conc t := refine (@GiC.Base.conc@{_} _ _ t _ _ _).

(** [path_elim p] は [refine (match p with idpath => _ end)] です。 *)

Ltac path_elim p := refine (match p with @GiC.Base.idpath _ _ => _ end).

(** ** 汎用的な関数の定義 *)

(** *** [conc] の変種 *)

(** 1-道の段階での [conc] です。 *)

(* from: originally defined by Hexirp *)
Definition conc1@{i | }
  {A : Type@{i}} {x y z : A}
  (p : Path@{i} x y) (q : Path@{i} y z)
  : Path@{i} x z
  := conc p q.

(** 2-道の段階での [conc] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/master/theories/Basics/PathGroupoids.v#L976 *)
Definition conc2@{i | }
  {A : Type@{i}} {x y z : A}
  {p p' : Path@{i} x y} {q q' : Path@{i} y z}
  (r : Path@{i} p p') (s : Path@{i} q q')
  : Path@{i} (conc1 p q) (conc1 p' q')
  := match s with idpath => match r with idpath => idpath end end.

(** 3-道の段階での [conc] です。 *)

(* from: originally defined by Hexirp *)
Definition conc3@{i | }
  {A : Type@{i}} {x y z : A}
  {p p' : Path@{i} x y} {q q' : Path@{i} y z}
  {r r' : Path@{i} p p'} {s s': Path@{i} q q'}
  (t : Path@{i} r r') (u : Path@{i} s s')
  : Path@{i} (conc2 r s) (conc2 r' s')
  := match u with idpath => match t with idpath => idpath end end.

(** *** [inv] の変種 *)

(** 1-道の段階での [inv] です。 *)

(* from: originally defined by Hexirp *)
Definition inv1@{i | }
  {A : Type@{i}} {x y : A} (p : Path@{i} x y)
  : Path@{i} y x
  := inv p.

(** 2-道の段階での [inv] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v#L993 *)
Definition inv2@{i | }
  {A : Type@{i}} {x y : A} {p q : Path@{i} x y} (r : Path@{i} p q)
  : Path@{i} (inv1 p) (inv1 q)
  := ap inv1 r.

(** 3-道の段階での [inv] です。 *)

(* from: originally defined by Hexirp *)
Definition inv3@{i | }
  {A : Type@{i}} {x y : A} {p q : Path@{i} x y}
  {r s : Path@{i} p q} (t : Path@{i} r s)
  : Path@{i} (inv2 r) (inv2 s)
  := ap inv2 t.

(** *** [ap] の変種 *)

(** 一変数関数に対する [ap] です。 *)

(* from: originally defined by Hexirp *)
Definition ap1@{i j | }
  {A : Type@{i}} {B : Type@{j}} (f : A -> B) {x x' : A} (p : Path@{i} x x')
  : Path@{j} (f x) (f x')
  := ap f p.

(** 二変数関数に対する [ap] です。 *)

(* from: originally defined by Hexirp *)
Definition ap2@{i j k | }
  {A : Type@{i}} {B : Type@{j}} {C : Type@{k}} (f : A -> B -> C)
  {x x' : A} (p : Path@{i} x x') {y y' : B} (q : Path@{j} y y')
  : Path@{k} (f x y) (f x' y')
  := match p with idpath => ap1 (f x) q end.

(** 三変数関数に対する [ap] です。 *)

(* from: originally defined by Hexirp *)
Definition ap3@{i j k l | }
  {A : Type@{i}} {B : Type@{j}} {C : Type@{k}} {D : Type@{l}}
  (f : A -> B -> C -> D)
  {x x' : A} (p : Path@{i} x x')
  {y y' : B} (q : Path@{j} y y')
  {z z' : C} (r : Path@{k} z z')
  : Path@{l} (f x y z) (f x' y' z')
  := match p with idpath => ap2 (f x) q r end.

(** 依存型に対応する [ap] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/Overture.v#L439 *)
Definition apD@{i j | }
  {A : Type@{i}} {B : A -> Type@{j}} (f : forall x : A, B x)
  {x y : A} (p : Path@{i} x y)
  : Path@{j} (trpt p (f x)) (f y)
  := match p with idpath => idpath end.

(** 関数の 0-道を値の 0-道に適用する関数です。 *)
(* from: originally defined by Hexirp *)
Definition ap00@{i j | }
  {A : Type@{i}} {B : Type@{j}}
  (f : A -> B) (x : A)
  : B
  := apply f x.

(** 関数の 0-道を値の 1-道に適用する関数です。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/Overture.v#L374 *)
Definition ap01@{i j | }
  {A : Type@{i}} {B : Type@{j}}
  (f : A -> B) {x x' : A} (pxx' : Path@{i} x x')
  : Path@{j} (f x) (f x')
  := ap f pxx'.

(** 関数の 1-道を値の 0-道に適用する関数です。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/Overture.v#L417 *)
Definition ap10@{i j mij | i <= mij, j <= mij}
  {A : Type@{i}} {B : Type@{j}}
  {f f' : A -> B} (pff' : Path@{mij} f f') (x : A)
  : Path@{j} (f x) (f' x)
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
Definition ap11@{i j mij | i <= mij, j <= mij}
  {A : Type@{i}} {B : Type@{j}}
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
