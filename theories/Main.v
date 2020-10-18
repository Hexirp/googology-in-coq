(* Run with -nois. *)

Require Import GiC.Core.

Unset Elimination Schemes.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Set Printing Universes.

Inductive Nat@{i} : Type@{i}
  := zero : Nat | succ : Nat -> Nat.

Definition pred@{i} (n : Nat@{i}) : Nat@{i} :=
  match n with zero => zero | succ np => np end.

Definition add@{i} (m n : Nat@{i}) : Nat@{i} :=
  let
    add_inner := fix add_inner (m n : Nat@{i}) {struct m} :=
      match m with zero => n | succ mp => succ (add_inner mp n) end
  in
    add_inner m n.
