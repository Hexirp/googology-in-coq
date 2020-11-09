(* Run with -nois. *)

(** 帰納原理 (induction principle) を自動的に生成しないように設定します。 *)
Unset Elimination Schemes.

(** 宇宙多相 (universe polymorphism) について設定します。 *)
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

(** 宇宙 (universe) について表示するように設定します。 *)
Set Printing Universes.

(** 関数の型を記号で書けるようにします。 *)
Notation "x -> y" := (forall (_ : x), y) (at level 99, right associativity, y at level 200).

(** ユニット型です。 *)
Inductive Unit@{i} : Type@{i} := unit : Unit.

(** ボトム型です。 *)
Inductive Void@{i} : Type@{i} :=.

(** 直積型です。 *)
Inductive Prod@{i j} (A : Type@{i}) (B : Type@{j}) : Type@{max(i,j)}
  := pair : A -> B -> Prod A B.

(** 直積型についての暗黙引数を設定します。 *)
Arguments pair {A} {B} a b.

(** 直積型の第一射影関数です。 *)
Definition fst@{i j} {A : Type@{i}} {B : Type@{j}} : Prod@{i j} A B -> A
  := fun x => match x with pair a b => a end.

(** 直積型の第二射影関数です。 *)
Definition snd@{i j} {A : Type@{i}} {B : Type@{j}} : Prod@{i j} A B -> B
  := fun x => match x with pair a b => b end.

(** 直和型です。 *)
Inductive Sum@{i j} (A : Type@{i}) (B : Type@{j}) : Type@{max(i,j)}
  := left : A -> Sum A B | right : B -> Sum A B.

(** 直和型についての暗黙引数を設定します。 *)
Arguments left {A} {B} a.
Arguments right {A} {B} b.

(** 依存和型です。 *)
Inductive DSum@{i j} (A : Type@{i}) (B : A -> Type@{j}) : Type@{max(i,j)}
  := dpair : forall a : A, B a -> DSum A B.

(** 依存和型についての暗黙引数を設定します。 *)
Arguments dpair {A} {B} a b.

(** 依存和型の第一射影関数です。 *)
Definition dfst@{i j} {A : Type@{i}} {B : A -> Type@{j}} (x : DSum@{i j} A B) : A
  := match x with dpair a b => a end.

(** 依存和型の第二射影関数です。 *)
Definition dsnd@{i j} {A : Type@{i}} {B : A -> Type@{j}} (x : DSum@{i j} A B) : B (dfst@{i j} x)
  := match x with dpair a b => b end.

(** 道型です。 *)
Inductive Path@{i} (A : Type@{i}) (a : A) : A -> Type@{i}
  := idpath : Path A a a.

(** 道型についての暗黙引数を設定します。 *)
(** idpath と書かれるときは idpath _ _ ですが idpath a と書かれるときは idpath _ a です。 *)
Arguments Path {A} a a'.
Arguments idpath {A} {a}, [A] a.

Definition idmap@{i} {A : Type@{i}} (x : A) : A := x.

Definition const@{i j} {A : Type@{i}} {B : Type@{j}} (x : A) (y : B) : A := x.

Definition comp@{i j k} {A : Type@{i}} {B : Type@{j}} {C : Type@{k}} (f : B -> C) (g : A -> B) (x : A) : C := f (g x).

Definition compD@{i j k} {A : Type@{i}} {B : Type@{j}} {C : B -> Type@{k}} (f : forall b : B, C b) (g : A -> B) (x : A) : C (g x) := f (g x).

Definition apply@{i j} {A : Type@{i}} {B : Type@{j}} (f : A -> B) (x : A) : B := f x.

Definition applyD@{i j} {A : Type@{i}} {B : A -> Type@{j}} (f : forall a : A, B a) (x : A) : B x := f x.

Definition absurd@{i j} {A : Type@{i}} (x : Void@{j}) : A
  := match x with end.

Definition curry@{i j k} {A : Type@{i}} {B : Type@{j}} {C : Type@{k}} (f : Prod@{i j} A B -> C) (x : A) (y : B) : C
  := f (pair x y).

Definition uncurry@{i j k} {A : Type@{i}} {B : Type@{j}} {C : Type@{k}} (f : A -> B -> C) (x : Prod@{i j} A B) : C
  := match x with pair a b => f a b end.

Definition inv@{i} {A : Type@{i}} {x y : A} (p : Path@{i} x y) : Path@{i} y x
  := match p with idpath => idpath end.

Definition conc@{i} {A : Type@{i}} {x y z : A} (p : Path@{i} x y) (q : Path@{i} y z) : Path@{i} x z
  := match q with idpath => match p with idpath => idpath end end.

Definition conv@{i} {A : Type@{i}} {x y z : A} (p : Path@{i} x y) (q : Path@{i} x z) : Path@{i} y z
  := conc@{i} (inv@{i} p) q.

Definition trpt@{i j} {A : Type@{i}} {B : A -> Type@{j}} {x y : A} (p : Path@{i} x y) (u : B x) : B y
  := match p with idpath => u end.

Definition trpv@{i j} {A : Type@{i}} {B : A -> Type@{j}} {x y : A} (p : Path@{i} x y) (u : B y) : B x
  := trpt@{i j} (inv@{i} p) u.

Definition ap@{i j} {A : Type@{i}} {B : Type@{j}} (f : A -> B) {x y : A} (p : Path@{i} x y) : Path@{j} (f x) (f y)
  := match p with idpath => idpath end.

Definition p_U_V@{i i' | i < i'} (p : Path@{i'} Unit@{i} Void@{i}) : Void@{i}
  := match p with idpath => unit@{i} end.
