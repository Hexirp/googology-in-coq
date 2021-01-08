(* Run with -nois. *)
(** [GiC.Type.Base] は基本的な型の定義を提供します。

    具体的には、 [Bool] や [Nat] などを定義します。
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

(** タクティックが使用できるように設定します。 *)

Set Default Proof Mode "Classic".

(** ビュレットを使用しないときにエラーになるように設定します。 *)

Set Default Goal Selector "!".

(** ** 単純な型 *)

(** ブーリアン型です。 *)

Inductive Bool@{i | } : Type@{i} :=
  | true : Bool
  | false : Bool.

(** ペアノの公理式の自然数の型です。 *)

Inductive Nat@{i | } : Type@{i} :=
  | zero : Nat
  | succ : Nat -> Nat.

(** 存在しないかもしれない値の型です。 *)

Inductive Option@{i | } (A : Type@{i}) : Type@{i} :=
  | none : Option A
  | some : A -> Option A.

(** [Option] 型の構築子の引数の暗黙性を設定します。 *)

Arguments some {A} _.

(** リストの型です。 *)

Inductive List@{i | } (A : Type@{i}) : Type@{i} :=
  | nil : List A
  | cons : A -> List A -> List A.

(** [List] 型の構築子の引数の暗黙性を設定します。 *)

Arguments nil {A}.
Arguments cons {A} _ _.

(** 比較の結果を表す型です。 *)

Inductive Comparison@{i | } : Type@{i} :=
  | eq : Comparison
  | lt : Comparison
  | gt : Comparison.
