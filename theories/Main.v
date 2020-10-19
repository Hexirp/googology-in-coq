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
      match m with zero => n | succ mp => succ@{i} (add_inner mp n) end
  in
    add_inner m n.

Definition mul@{i} (m n : Nat@{i}) : Nat@{i} :=
  let
    mul_inner := fix mul_inner (m n : Nat@{i}) {struct m} :=
      match m with zero => zero@{i} | succ mp => add@{i} n (mul_inner mp n) end
  in
    mul_inner m n.

Definition sub@{i} (m n : Nat@{i}) : Nat@{i} :=
  let
    sub_inner := fix sub_inner (m n : Nat@{i}) {struct m} :=
      match m with
      | zero => zero@{i}
      | succ mp =>
        match n with
        | zero => succ@{i} mp
        | succ np => sub_inner mp np
        end
      end
  in
    sub_inner m n.
