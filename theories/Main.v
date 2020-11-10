(* Run with -nois. *)

Require Import GiC.Core.

(** 帰納原理 (induction principle) を生成しないように設定します。 *)
Unset Elimination Schemes.

(** 宇宙多相 (universe polymorphism) について設定します。 *)
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

(** 宇宙 (universe) について表示するように設定します。 *)
Set Printing Universes.

Definition conc_p_1@{i} {A : Type@{i}} {x y : A}
  : forall p : Path@{i} x y, Path@{i} (conc@{i} p idpath) p
  := fun p => match p with idpath => idpath end.

Definition conc_1_p@{i} {A : Type@{i}} {x y : A}
  : forall p : Path@{i} x y, Path@{i} (conc@{i} idpath p) p
  := fun p => match p with idpath => idpath end.
