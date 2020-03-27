Unset Elimination Schemes.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Inductive Unit@{i} : Type@{i} := unit : Unit.

Notation "x -> y" := (forall (_ : x), y) (at level 99, right associativity, y at level 200).
