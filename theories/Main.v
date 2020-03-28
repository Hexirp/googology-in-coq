Unset Elimination Schemes.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Set Printing Universes.

Notation "x -> y" := (forall (_ : x), y) (at level 99, right associativity, y at level 200).

Inductive Unit@{i} : Type@{i} := unit : Unit.

Inductive Void@{i} : Type@{i} :=.

Inductive Sum@{i j} (A : Type@{i}) (B : Type@{j}) : Type@{max(i,j)} :=
  | left : A -> Sum A B
  | right : B -> Sum A B.

Print Sum.
