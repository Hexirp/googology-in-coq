(* Run with -nois. *)
(** [GiC.Base] は、全ての基礎となる型や関数などを定義します。

    具体的には、一階述語論理に対応する型と、それに関する本当に単純な関数を提供しています。
 *)

(** Coq と SSReflect のタクティックを使用するためにプラグインを読み込みます。 *)

Declare ML Module "ltac_plugin".
Declare ML Module "ssrmatching_plugin".
Declare ML Module "ssreflect_plugin".

(** タクティックが使用できるように設定します。 *)

Set Default Proof Mode "Classic".

(** ビュレットを使用しないときにエラーになるように設定します。 *)

Set Default Goal Selector "!".

(** 帰納原理 (induction principle) を生成しないように設定します。 *)

Unset Elimination Schemes.

(** 宇宙多相 (universe polymorphism) について設定します。 *)

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

(** 関数の型を記号で書けるようにします。 *)

Notation
  "x -> y"
    := (forall (_ : x), y)
  (at level 99, right associativity, y at level 200)
.

(** 関数型です。 *)

Module Function.

(** 主型の等しさです。 *)

Definition T_ (A : Type) (A_ : A -> A -> Type) (B : Type) (B_ : B -> B -> Type)
  : (A -> B) -> (A -> B) -> Type
  :=
    fun (f : A -> B) (g : A -> B) =>
      forall x : A, forall y : A, A_ x y -> B_ (f x) (g y)
.

(** 恒等関数です。 *)

(* from: originally defined by Hexirp *)
Definition id {A : Type}
  : A -> A
  := fun x : A => x
.

(** 定数関数です。 *)

(* from: originally defined by Hexirp *)
Definition const {A : Type} {B : Type}
  : A -> B -> A
  := fun x : A => fun y : B => x
.

(** 関数の合成です。 *)

(* from: originally defined by Hexirp *)
Definition comp {A : Type} {B : Type} {C : Type}
  : (B -> C) -> (A -> B) -> A -> C
  := fun (f : B -> C) (g : A -> B) (x : A) => f (g x)
.

(** 関数の適用です。 *)

(* from: originally defined by Hexirp *)
Definition apply {A : Type} {B : Type}
  : (A -> B) -> A -> B
  := fun (f : A -> B) (x : A) => f x
.

End Function.

(** 依存関数型です。 *)

Module Dependent_Function.

(** 関数の適用です。 *)

(* from: originally defined by Hexirp *)
Definition apply {A : Type} {B : A -> Type}
  : (forall x : A, B x) -> forall x : A, B x
  := fun (f : forall x : A, B x) (x : A) => f x
.

End Dependent_Function.

(** ユニット型です。 *)

Module Unit.

(** 主型です。 *)

(* from: originally defined by Hexirp *)
Inductive T
  : Type
  := unit : T
.

End Unit.

(** ボトム型です。 *)

Module Void.

(** 主型です。 *)

(* from: originally defined by Hexirp *)
Inductive T
  : Type
  :=
.

(** 矛盾による証明です。 *)

(* from: originally defined by Hexirp *)
Definition absurd {A : Type}
  : T -> A
  := fun x => match x with end
.

End Void.

(** 直積型です。 *)

Module Product.

(** 主型です。 *)

(* from: originally defined by Hexirp *)
Inductive T (A : Type) (B : Type) : Type := pair : A -> B -> T A B.

(** [pair] についての暗黙引数を設定します。 *)

Arguments pair {A} {B} a b.

(** 直積型の第一射影関数です。 *)

(* from: originally defined by Hexirp *)
Definition first {A : Type} {B : Type} : T A B -> A
  := fun x : T A B => match x with pair a b => a end
.

(** 直積型の第二射影関数です。 *)

(* from: originally defined by Hexirp *)
Definition second {A : Type} {B : Type} : T A B -> B
  := fun x : T A B => match x with pair a b => b end
.

(** 関数のカリー化です。 *)

(* from: originally defined by Hexirp *)
Definition curry {A : Type} {B : Type} {C : Type}
  : (T A B -> C) -> A -> B -> C
  := fun (f : T A B -> C) (x : A) (y : B) => f (pair x y)
.

(** 関数の非カリー化です。 *)

(* from: originally defined by Hexirp *)
Definition uncurry {A : Type} {B : Type} {C : Type}
  : (A -> B -> C) -> T A B -> C
  :=
    fun (f : A -> B -> C) (x : T A B) =>
      match x with pair a b => f a b end
.

End Product.

(** 直和型です。 *)

Module Sum.

(** 主型です。 *)

(* from: originally defined by Hexirp *)
Inductive T (A : Type) (B : Type)
  : Type
  := left : A -> T A B | right : B -> T A B
.

(** [left] についての暗黙引数を設定します。 *)

Arguments left {A} {B} a.

(** [right] についての暗黙引数を設定します。 *)

Arguments right {A} {B} b.

End Sum.

(** 依存積型です。 *)

Module Dependent_Product.

(** 主型です。 *)

(* from: originally defined by Hexirp *)
Inductive T (A : Type) (B : A -> Type)
  : Type
  := wrap : (forall a : A, B a) -> T A B
.

(** [value] についての暗黙引数を設定します。 *)

Arguments wrap {A} {B} _.

(** 包みを剥がす関数です。 *)

(* from: originally defined by Hexirp *)
Definition unwrap {A : Type} {B : A -> Type}
  : T A B -> forall a : A, B a
  := fun x : T A B => match x with wrap x_v => x_v end
.

End Dependent_Product.

(** 依存和型です。 *)

Module Dependent_Sum.

(** 主型です。 *)

(* from: originally defined by Hexirp *)
Inductive T (A : Type) (B : A -> Type)
  : Type
  := pair : forall a : A, B a -> T A B
.

(** [pair] についての暗黙引数を設定します。 *)

Arguments pair {A} {B} a b.

(** 依存和型の第一射影関数です。 *)

(* from: originally defined by Hexirp *)
Definition first {A : Type} {B : A -> Type}
  : T A B -> A
  := fun x => match x with pair a b => a end
.

(** 依存和型の第二射影関数です。 *)

(* from: originally defined by Hexirp *)
Definition second {A : Type} {B : A -> Type}
  : forall x : T A B, B (first x)
  := fun x => match x with pair a b => b end
.

End Dependent_Sum.

(** 道型です。 *)

Module Path.

(** 主型です。 *)

(* from: originally defined by Hexirp *)
Private Inductive T (A : Type) (a : A) 
  : A -> Type
  := id : T A a a
.

(** 道型についての暗黙引数を設定します。 *)

Arguments T {A} a a'.

(** [id] についての暗黙引数を設定します。

    [id] と書いたときは [id _ _] と補われます。 [id a] と書いたときは [idpath _ a] と補われます。
 *)

Arguments id {A} {a}, [A] a.

(** 道の逆です。 *)

(* from: originally defined by Hexirp *)
Definition inv {A : Type} {x y : A}
  : T x y -> T y x
  := fun p : T x y => match p with id => id end
.

(** 道の結合です。 *)

(* from: originally defined by Hexirp *)
Definition conc {A : Type} {x y z : A}
  : T x y -> T y z -> T x z
  :=
    fun (p : T x y) (q : T y z) =>
      match q with id => match p with id => id end end
.

(** 道の結合と逆です。 *)

(* from: originally defined by Hexirp *)
Definition conv {A : Type} {x y z : A}
  : T x y -> T x z -> T y z
  := fun (p : T x y) (q : T x z) => conc (inv p) q
.

(** 道による輸送です。 *)

(* from: originally defined by Hexirp *)
Definition trpt {A : Type} {B : A -> Type} {x y : A}
  : T x y -> B x -> B y
  := fun (p : T x y) (u : B x) => match p with id => u end
.

(** 道による輸送と逆です。 *)

(* from: originally defined by Hexirp *)
Definition trpv {A : Type} {B : A -> Type} {x y : A}
  : T x y -> B y -> B x
  := fun (p : T x y) (u : B y) => trpt (inv p) u
.

(** 道への適用です。 *)

(* from: originally defined by Hexirp *)
Definition ap {A : Type} {B : Type} (f : A -> B) {x y : A}
  : T x y -> T (f x) (f y)
  := fun p : T x y => match p with id => id end
.

End Path.

(** 点ごとの道です。 *)

Module Pointwise_Path.

(** 主型です。 *)

(* from: originally defined by Hexirp *)
Definition T (A : Type) (B : Type)
  : (A -> B) -> (A -> B) -> Type
  :=
    fun (f : A -> B) (g : A -> B) =>
      forall x : A, Path.T (f x) (g x)
.

(** [Function.T_] への変換です。 *)

(* from: originally defined by Hexirp *)
Definition to_Function_1 (A : Type) (B : Type)
  :
    forall (f : A -> B) (g : A -> B),
      T A B f g -> Function.T_ A (@Path.T A) B (@Path.T B) f g
.
Proof.
  move=> f g.
  unfold T; unfold Function.T_.
  move=> h.
  move=> x y.
  move=> p.
  refine (let D := fun y : A => Path.T (f x) (g y) in _).
  change (D y).
  refine (Path.trpt p _).
  exact (h x).
Defined.

(** [Function.T_] からの変換です。 *)

(* from: originally defined by Hexirp *)
Definition from_Function_1 (A : Type) (B : Type)
  :
    forall (f : A -> B) (g : A -> B),
      Function.T_ A (@Path.T A) B (@Path.T B) f g -> T A B f g
.
Proof.
  move=> f g.
  unfold Function.T_; unfold T.
  move=> h.
  move=> x.
  exact (h x x Path.id).
Defined.

End Pointwise_Path.
