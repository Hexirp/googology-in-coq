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
  : forall p : Path@{i} x y, Path@{i} (conc p idpath) p
  := fun p => match p with idpath => idpath end.

Definition conc_1_p@{i} {A : Type@{i}} {x y : A}
  : forall p : Path@{i} x y, Path@{i} (conc idpath p) p
  := fun p => match p with idpath => idpath end.

Definition conc_p_cqr@{i} {A : Type@{i}} {x y z w : A}
  : forall (p : Path@{i} x y) (q : Path@{i} y z) (r : Path@{i} z w), Path@{i} (conc p (conc q r)) (conc (conc p q) r)
  := fun p q r => match r with idpath => match q with idpath => match p with idpath => idpath end end end.

Definition conc_cpq_r@{i} {A : Type@{i}} {x y z w : A}
  : forall (p : Path@{i} x y) (q : Path@{i} y z) (r : Path@{i} z w), Path@{i} (conc (conc p q) r) (conc p (conc q r))
  := fun p q r => match r with idpath => match q with idpath => match p with idpath => idpath end end end.

Definition conc_p_vp@{i} {A : Type@{i}} {x y : A}
  : forall p : Path@{i} x y, Path@{i} (conc p (inv p)) idpath
  := fun p => match p with idpath => idpath end.

Definition conc_vp_p@{i} {A : Type@{i}} {x y : A}
  : forall p : Path@{i} x y, Path@{i} (conc (inv p) p) idpath
  := fun p => match p with idpath => idpath end.
