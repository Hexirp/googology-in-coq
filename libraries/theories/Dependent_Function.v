(** 依存関数型のモジュールです。 *)

Require Googology_In_Coq.Base.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.

(** ライブラリを開きます。 *)

Definition
  Dependent_Function@{i | } (A : Type@{i}) (B : A -> Type@{i}) : Type@{i}
    := forall x : A, B x
.
(* from: originally defined by Hexirp *)

(** 依存関数型です。 *)

Definition
  abstract@{i | } (A : Type@{i}) (B : A -> Type@{i}) (x : forall x : A, B x)
    : Dependent_Function@{i} A B
    := x
.

(** 抽象です。ラムダ抽象です。 *)

Definition
  apply@{i | }
      (A : Type@{i})
      (B : A -> Type@{i})
      (x : Dependent_Function@{i} A B)
    : forall x : A, B x
    := x
.

(** 適用です。 *)

(** [abstract] は構築子です。 [apply] は分解子です。甲を [abstract] で構築したものを [apply] で分解したものは甲と同じというのが β-変換です。甲を [apply] で分解したものを [abstract] で構築したものは甲と同じというのが η-変換です。「全てのイに対して甲をイに適用したものと乙をイに適用したものが同じである」であれば甲を [abstract] で構築したものと乙を [abstract] で構築したものが同じというのが判断同値の関数外延性です。甲と乙が同じかつイとロが同じであれば甲を [apply] で分解したものをイに適用したものと乙を [apply] で分解したものをロに適用したものは同じであるというのがホニャララです。 *)
