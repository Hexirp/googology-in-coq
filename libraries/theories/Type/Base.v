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

(** タクティックが使用できるように設定します。 *)

Set Default Proof Mode "Classic".

(** ビュレットを使用しないときにエラーになるように設定します。 *)

Set Default Goal Selector "!".

(** ** 基本的な型 *)

(** ブーリアン型です。 *)

(* from: originally defined by Hexirp *)
Inductive Bool@{i | } : Type@{i} :=
  | true : Bool
  | false : Bool.

(** ペアノの公理式の自然数の型です。 *)

(* from: originally defined by Hexirp *)
Inductive Nat@{i | } : Type@{i} :=
  | zero : Nat
  | succ : Nat -> Nat.

(** 存在しないかもしれない値の型です。 *)

(* from: originally defined by Hexirp *)
Inductive Option@{i | } (A : Type@{i}) : Type@{i} :=
  | none : Option A
  | some : A -> Option A.

(** [Option] 型の構築子の引数の暗黙性を設定します。 *)

Arguments some {A} _.

(** リストの型です。 *)

(* from: originally defined by Hexirp *)
Inductive List@{i | } (A : Type@{i}) : Type@{i} :=
  | nil : List A
  | cons : A -> List A -> List A.

(** [List] 型の構築子の引数の暗黙性を設定します。 *)

Arguments nil {A}.
Arguments cons {A} _ _.

(** 比較の結果を表す型です。 *)

(* from: originally defined by Hexirp *)
Inductive Comparison@{i | } : Type@{i} :=
  | eq : Comparison
  | lt : Comparison
  | gt : Comparison.

(** ** 切り捨て (truncation) *)

(* from: originally defined by Hexirp *)
Inductive IsContr@{i | } (A : Type@{i}) : Type@{i} :=
  | make_IsContr : forall x : A, (forall y : A, Path@{i} x y) -> IsContr A.

(* from: originally defined by Hexirp *)
Definition IsTrunc@{i | } (n : Nat@{i}) (A : Type@{i}) : Type@{i}
  :=
    let
      t0 :=
        fix t1 (n : Nat@{i}) (A : Type@{i}) {struct n} : Type@{i} :=
          match n
            with
              | zero => IsContr@{i} A
              | succ np => forall (x y : A), t1 np (Path@{i} x y)
          end
    in
      t0 n A.

(** ** 反射 (reflection) *)

(* from: originally defined by Hexirp *)
Inductive IsTrue@{i | } (x : Bool@{i}) : Type@{i} :=
  | make_IsTrue : Path@{i} x true -> IsTrue x.

(* from: originally defined by Hexirp *)
Inductive IsDecidable@{i | } (A : Type@{i}) : Type@{i} :=
  | pos_IsDecidable : A -> IsDecidable A
  | neg_IsDecidable : (A -> Void@{i}) -> IsDecidable A.

(* from: originally defined by Hexirp *)
Inductive Reflect@{i | } (A : Type@{i}) (x : Bool@{i}) : Type@{i} :=
  | pos_Reflect : A -> Path@{i} x true -> Reflect A x
  | neg_Reflect : (A -> Void@{i}) -> Path@{i} x false -> Reflect A x.

(* from: originally defined by Hexirp *)
Inductive IsStronglyDecidable@{i | } (A : Type@{i}) : Type@{i} :=
  | pos_IsStronglyDecidable : IsContr A -> IsStronglyDecidable A
  | neg_IsStronglyDecidable : (A -> Void@{i}) -> IsStronglyDecidable A.

(* from: originally defined by Hexirp *)
Inductive StronglyReflect@{i | } (A : Type@{i}) (x : Bool@{i}) : Type@{i} :=
  | pos_StronglyReflect
    : IsContr A -> Path@{i} x true -> StronglyReflect A x
  | neg_StronglyReflect
    : (A -> Void@{i}) -> Path@{i} x false -> StronglyReflect A x.
