(* Run with -nois. *)

(** * GiC.Base *)

(** [GiC.Base] は、全ての基礎となる型や関数などを定義します。

    具体的には、一階述語論理に対応する型と、それに関する本当に単純な関数を提供しています。
 *)

(** Coq と SSReflect のタクティックを使用するためにプラグインを読み込みます。 *)
Declare ML Module "ltac_plugin".
Declare ML Module "ssrmatching_plugin".
Declare ML Module "ssreflect_plugin".

(** 帰納原理 (induction principle) を生成しないように設定します。 *)
Unset Elimination Schemes.

(** 宇宙多相 (universe polymorphism) について設定します。 *)
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

(** 宇宙 (universe) について表示するように設定します。 *)
Set Printing Universes.

(** 関数の型を記号で書けるようにします。 *)
Notation "x -> y" := (forall (_ : x), y) (at level 99, right associativity, y at level 200).

(** ユニット型です。 *)
(* from: originally defined by Hexirp *)
Inductive Unit@{i | } : Type@{i} := unit : Unit.

(** ボトム型です。 *)
(* from: originally defined by Hexirp *)
Inductive Void@{i | } : Type@{i} :=.

(** 直積型です。 *)
(* from: originally defined by Hexirp *)
Inductive Prod@{i j | } (A : Type@{i}) (B : Type@{j}) : Type@{max(i,j)}
  := pair : A -> B -> Prod A B.

(** 直積型についての暗黙引数を設定します。 *)
Arguments pair {A} {B} a b.

(** 直積型の第一射影関数です。 *)
(* from: originally defined by Hexirp *)
Definition fst@{i j | } {A : Type@{i}} {B : Type@{j}}
  : Prod@{i j} A B -> A
  := fun x => match x with pair a b => a end.

(** 直積型の第二射影関数です。 *)
(* from: originally defined by Hexirp *)
Definition snd@{i j | } {A : Type@{i}} {B : Type@{j}}
  : Prod@{i j} A B -> B
  := fun x => match x with pair a b => b end.

(** 直和型です。 *)
(* from: originally defined by Hexirp *)
Inductive Sum@{i j | } (A : Type@{i}) (B : Type@{j}) : Type@{max(i,j)}
  := left : A -> Sum A B | right : B -> Sum A B.

(** 直和型についての暗黙引数を設定します。 *)
Arguments left {A} {B} a.
Arguments right {A} {B} b.

(** 依存和型です。 *)
(* from: originally defined by Hexirp *)
Inductive DSum@{i j | } (A : Type@{i}) (B : A -> Type@{j}) : Type@{max(i,j)}
  := dpair : forall a : A, B a -> DSum A B.

(** 依存和型についての暗黙引数を設定します。 *)
Arguments dpair {A} {B} a b.

(** 依存和型の第一射影関数です。 *)
(* from: originally defined by Hexirp *)
Definition dfst@{i j | } {A : Type@{i}} {B : A -> Type@{j}}
  : DSum@{i j} A B -> A
  := fun x => match x with dpair a b => a end.

(** 依存和型の第二射影関数です。 *)
(* from: originally defined by Hexirp *)
Definition dsnd@{i j | } {A : Type@{i}} {B : A -> Type@{j}}
  : forall x : DSum@{i j} A B, B (dfst@{i j} x)
  := fun x => match x with dpair a b => b end.

(** 道型です。 *)
(* from: originally defined by Hexirp *)
Inductive Path@{i | } (A : Type@{i}) (a : A) : A -> Type@{i}
  := idpath : Path A a a.

(** 道型についての暗黙引数を設定します。

    [idpath] と書いたときは [idpath _ _] と補われます。 [idpath a] と書いたときは [idpath _ a] と補われます。
 *)
Arguments Path {A} a a'.
Arguments idpath {A} {a}, [A] a.

(** 恒等関数です。 *)
(* from: originally defined by Hexirp *)
Definition idmap@{i | } {A : Type@{i}}
  : A -> A
  := fun x => x.

(** 定数関数です。 *)
(* from: originally defined by Hexirp *)
Definition const@{i j | } {A : Type@{i}} {B : Type@{j}}
  : A -> B -> A
  := fun x y => x.

(** 関数の合成です。 *)
(* from: originally defined by Hexirp *)
Definition comp@{i j k | } {A : Type@{i}} {B : Type@{j}} {C : Type@{k}}
  : (B -> C) -> (A -> B) -> A -> C
  := fun f g x => f (g x).

(** 関数の適用です。 *)
(* from: originally defined by Hexirp *)
Definition apply@{i j | } {A : Type@{i}} {B : Type@{j}}
  : (A -> B) -> A -> B
  := fun f x => f x.

(** 矛盾による証明です。 *)
(* from: originally defined by Hexirp *)
Definition absurd@{i j | } {A : Type@{i}}
  : Void@{j} -> A
  := fun x => match x with end.

(** 関数のカリー化です。 *)
(* from: originally defined by Hexirp *)
Definition curry@{i j k | } {A : Type@{i}} {B : Type@{j}} {C : Type@{k}}
  : (Prod@{i j} A B -> C) -> A -> B -> C
  := fun f x y => f (pair x y).

(** 関数の非カリー化です。 *)
(* from: originally defined by Hexirp *)
Definition uncurry@{i j k | } {A : Type@{i}} {B : Type@{j}} {C : Type@{k}}
  : (A -> B -> C) -> Prod@{i j} A B -> C
  := fun f x => match x with pair a b => f a b end.

(** 道の逆です。 *)
(* from: originally defined by Hexirp *)
Definition inv@{i | } {A : Type@{i}} {x y : A}
  : Path@{i} x y -> Path@{i} y x
  := fun p => match p with idpath => idpath end.

(** 道の結合です。 *)
(* from: originally defined by Hexirp *)
Definition conc@{i | } {A : Type@{i}} {x y z : A}
  : Path@{i} x y -> Path@{i} y z -> Path@{i} x z
  := fun p q => match q with idpath => match p with idpath => idpath end end.

(** 道の結合と逆です。 *)
(* from: originally defined by Hexirp *)
Definition conv@{i | } {A : Type@{i}} {x y z : A}
  : Path@{i} x y -> Path@{i} x z -> Path@{i} y z
  := fun p q => conc@{i} (inv@{i} p) q.

(** 道による輸送です。 *)
(* from: originally defined by Hexirp *)
Definition trpt@{i j | } {A : Type@{i}} {B : A -> Type@{j}} {x y : A}
  : Path@{i} x y -> B x -> B y
  := fun p u => match p with idpath => u end.

(** 道による輸送と逆です。 *)
(* from: originally defined by Hexirp *)
Definition trpv@{i j | } {A : Type@{i}} {B : A -> Type@{j}} {x y : A}
  : Path@{i} x y -> B y -> B x
  := fun p u => trpt@{i j} (inv@{i} p) u.

(** 道への適用です。 *)
(* from: originally defined by Hexirp *)
Definition ap@{i j | } {A : Type@{i}} {B : Type@{j}} (f : A -> B) {x y : A}
  : Path@{i} x y -> Path@{j} (f x) (f y)
  := fun p => match p with idpath => idpath end.

(** [Path Unit Void] です。

    この関数は仲間外れですが、そこがいいのです。
 *)
(* from: originally defined by Hexirp *)
Definition p_U_V@{i si | i < si}
  : Path@{si} Unit@{i} Void@{i} -> Void@{i}
  := fun p => match p with idpath => unit@{i} end.
