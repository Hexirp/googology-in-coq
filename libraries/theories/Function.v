(* Run with -nois. *)

(** * GiC.Function *)

(** GiC.Function は、関数に関する定義を提供します。

    具体的には、変数の抽象化と適用だけで表現できるような様々な高階関数と、それらに関わる単純な等式を提供します。
 *)

(** 必要なライブラリを要求します。 *)
Require GiC.Base.

(** 必要なライブラリをインポートします。 *)
Import GiC.Base.

(** 帰納原理 (induction principle) を生成しないように設定します。 *)
Unset Elimination Schemes.

(** 宇宙多相 (universe polymorphism) について設定します。 *)
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

(** 宇宙 (universe) について表示するように設定します。 *)
Set Printing Universes.

(** 二変数関数の引数を入れ替えます。 *)
(* from: originally defined by Hexirp *)
Definition flip@{i j k | } {A : Type@{i}} {B : Type@{j}} {C : Type@{k}}
  : (A -> B -> C) -> B -> A -> C
  := fun f x y => f y x.

(** 第二変数を第一変数に適用します。 *)
(* from: originally defined by Hexirp *)
Definition dot@{i j | } {A : Type@{i}} {B : Type@{j}}
  : A -> (A -> B) -> B
  := fun x f => f x.

(** 依存関数に対応する [comp] です。 *)
(* from: originally defined by Hexirp *)
Definition compD@{i j k | } {A : Type@{i}} {B : Type@{j}} {C : B -> Type@{k}}
  : (forall b : B, C b) -> forall (g : A -> B) (a : A), C (g a)
  := fun f g x => f (g x).

(** 依存関数に対応する [apply] です。 *)
(* from: originally defined by Hexirp *)
Definition applyD@{i j | } {A : Type@{i}} {B : A -> Type@{j}}
  : (forall a : A, B a) -> forall (a : A), B a
  := fun f x => f x.

(** 非依存型 [B] から非依存型 [C] への関数と、非依存型 [A] から非依存型 [B] への関数の合成です。 *)
(* from: originally defined by Hexirp *)
Definition compNNN@{i j k | }
  {A : Type@{i}} {B : Type@{j}} {C : Type@{k}}
  : (B -> C) -> (A -> B) -> A -> C
  := comp.

(** 非依存型 [B] から依存型 [C b] への関数と、非依存型 [A] から非依存型 [B] への関数の合成です。 *)
(* from: originally defined by Hexirp *)
Definition compNND@{i j k | }
  {A : Type@{i}} {B : Type@{j}} {C : B -> Type@{k}}
  : (forall b : B, C b) -> forall (g : A -> B) (a : A), C (g a)
  := compD.

(** 依存型 [B a] から非依存型 [C] への関数と、非依存型 [A] から依存型 [B a] への関数の合成です。 *)
(* from: originally defined by Hexirp *)
Definition compNDN@{i j k | }
  {A : Type@{i}} {B : A -> Type@{j}} {C : Type@{k}}
  : (forall a : A, B a -> C) -> (forall a : A, B a) -> A -> C
  := fun f g x => f x (g x).

(** 依存型 [B a] から依存型 [C a b] への関数と、非依存型 [A] から依存型 [B a] への関数の合成です。 *)
(* from: originally defined by Hexirp *)
Definition compNDD@{i j k | }
  {A : Type@{i}} {B : A -> Type@{j}} {C : forall a : A, B a -> Type@{k}}
  : (forall (a : A) (b : B a), C a b) ->
    forall (g : forall a : A, B a) (a : A), C a (g a)
  := fun f g x => f x (g x).
