(* Run with -nois. *)
(** [GiC.Type.Base] は基本的な型の定義を提供します。

    具体的には、 [Bool] や [Nat] などを定義します。
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

(** 点ごとの道 (pointwise path) です。 *)

(* from: originally defined by Hexirp *)
Definition PwPath@{i j mij | i <= mij, j <= mij }
  (A : Type@{i}) (B : A -> Type@{j}) (f g : forall x : A, B x)
  : Type@{mij}
  := forall x : A, Path@{j} (f x) (g x).

(** 依存関数に対応しない点ごとの道 (pointwise path) です。 *)

(* from: originally defined by Hexirp *)
Definition PwPathN@{i j mij | i <= mij, j <= mij }
  {A : Type@{i}} {B : Type@{j}} (f g : A -> B)
  : Type@{mij}
  := forall x : A, PwPath@{i j mij} A (fun _ => B) f g.

(** ** 基本的な汎用関数 *)

(** [Path A B -> A -> B] です。 *)

(* from: originally defined by Hexirp *)
Definition cast@{i si | i < si} (A : Type@{i}) (B : Type@{i})
  : Path@{si} A B -> A -> B
  := fun p x => match p in Path _ B_ return B_ with idpath => x end.

(** [Path Unit Void -> Void] です。 *)

(* from: originally defined by Hexirp *)
Definition pUV@{i si | i < si}
  : Path@{si} Unit@{i} Void@{i} -> Void@{i}
  := fun p => match p with idpath => unit@{i} end.

(** ** 反射 (reflection) *)

(** [x] が [true] であることです。 *)

(* from: originally defined by Hexirp *)
Inductive IsTrue@{i | } (x : Bool@{i}) : Type@{i} :=
  | make_IsTrue : Path@{i} x true -> IsTrue x.

(** [A] が決定可能であることです。 *)

(* from: originally defined by Hexirp *)
Inductive IsDecidable@{i | } (A : Type@{i}) : Type@{i} :=
  | pos_IsDecidable : A -> IsDecidable A
  | neg_IsDecidable : (A -> Void@{i}) -> IsDecidable A.

(** [A] が [x] に反射していることです。 *)

(* from: originally defined by Hexirp *)
Inductive Reflect@{i | } (A : Type@{i}) (b : Bool@{i}) : Type@{i} :=
  | pos_Reflect : A -> Path@{i} b true -> Reflect A b
  | neg_Reflect : (A -> Void@{i}) -> Path@{i} b false -> Reflect A b.

(** [A] が強く決定可能であることです。 *)

(* from: originally defined by Hexirp *)
Inductive IsStronglyDecidable@{i | } (A : Type@{i}) : Type@{i} :=
  | pos_IsStronglyDecidable
    : forall x : A, (forall y : A, Path@{i} x y) -> IsStronglyDecidable A
  | neg_IsStronglyDecidable : (A -> Void@{i}) -> IsStronglyDecidable A.

(** [A] が [x] に強く反射していることです。 *)

(* from: originally defined by Hexirp *)
Inductive StronglyReflect@{i | } (A : Type@{i}) (b : Bool@{i}) : Type@{i} :=
  | pos_StronglyReflect
    : forall x : A,
      (forall y : A, Path@{i} x y) -> Path@{i} b true -> StronglyReflect A b
  | neg_StronglyReflect
    : (A -> Void@{i}) -> Path@{i} b false -> StronglyReflect A b.

(** ** 方程式による推論 (equational reasoning) *)

(** いくつかの等式を繋ぎ合わせた等式です。 *)

(* from: originally defined by Hexirp *)
Inductive PathStep@{i | } {A : Type@{i}} (x y : A) : Type@{i} :=
  | nil_PathStep : Path@{i} x y -> PathStep x y
  | cons_PathStep
    : forall x' : A, PathStep x x' -> Path@{i} x' y -> PathStep x y.

Arguments nil_PathStep {A x y} p.
Arguments cons_PathStep {A x y} x' p q.

(** [PathStep x y -> Path x y] です。 *)

(* from: originally defined by Hexirp *)
Definition fun_PathStep_x_y_Path_x_y@{i | } {A : Type@{i}} {x y : A}
  : PathStep@{i} x y -> Path@{i} x y
  :=
    let
      t0
        :=
          fix t1 (y : A) (p : PathStep@{i} x y) {struct p} : Path@{i} x y :=
            match p
              with
                | nil_PathStep h => h
                | cons_PathStep y' p' h => conc (t1 y' p') h
            end
    in
      t0 y.

(** equational reasoning 専用の scope を定義します。 *)

Declare Scope equational_reasoing_scope.
Delimit Scope equational_reasoing_scope with equational_reasoing.
Open Scope equational_reasoing_scope.

(** equational reasoning を開始する notation を定義します。 *)

(* from: originally defined by Hexirp *)
Notation "[= x =]"
  := (@nil_PathStep@{_} _ x x (@GiC.Base.idpath@{_} _ x))
  (at level 99, no associativity)
  : equational_reasoing_scope.

(** equational reasoning の notation を定義します。 *)

(* from: originally defined by Hexirp *)
Notation "p =[ q ] y"
  := (@cons_PathStep@{_} _ _ y _ p q)
  (at level 100, right associativity)
  : equational_reasoing_scope.

(** 方程式による推論 (equational reasoning) を行うタクティックです。 *)

(* from: originally defined by Hexirp *)
Ltac step x
  := refine (@fun_PathStep_x_y_Path_x_y@{_} _ _ _ (x%equational_reasoing)).

(** ** 切り捨て (truncation) *)

(** [A] が可縮 (contractible) であることです。 *)

(* from: originally defined by Hexirp *)
Inductive IsContr@{i | } (A : Type@{i}) : Type@{i} :=
  | make_IsContr : forall x : A, (forall y : A, Path@{i} x y) -> IsContr A.

(** [A] が (n-2)-切り捨て (truncated) であることです。 *)

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

(** [A] が命題的であることです。 *)

(* from: originally defined by Hexirp *)
Definition IsProp@{i | } (A : Type@{i}) : Type@{i}
  := IsTrunc (succ zero) A.

(** [A] が集合的であることです。 *)

(* from: originally defined by Hexirp *)
Definition IsSet@{i | } (A : Type@{i}) : Type@{i}
  := IsTrunc (succ (succ zero)) A.

(** ** 等価性 (equivalence) *)

(** [f] は等価写像である。 *)

(* from: https://github.com/HoTT/HoTT/blob/46f10ef3c7218b912c6686ecec650e728c69085e/theories/Basics/Overture.v#L466 *)
Inductive IsEquiv@{i | } {A B : Type@{i}} (f : A -> B) : Type@{i} :=
  | make_IsEquiv
    : forall
      (g : B -> A)
      (r : forall x : B, Path@{i} (f (g x)) x)
      (s : forall x : A, Path@{i} (g (f x)) x),
      (forall x : A, Path@{i} (r (f x)) (ap f (s x))) -> IsEquiv f.

(** [A] と [B] は等価 (equivalence) である。 *)

(* from: https://github.com/HoTT/HoTT/blob/46f10ef3c7218b912c6686ecec650e728c69085e/theories/Basics/Overture.v#L479 *)
Inductive Equiv@{i | } (A B : Type@{i}) : Type@{i} :=
  | make_Equiv : forall f : A -> B, IsEquiv f -> Equiv A B.
