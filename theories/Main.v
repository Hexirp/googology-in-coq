Unset Elimination Schemes.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Set Printing Universes.

Notation "x -> y" := (forall (_ : x), y) (at level 99, right associativity, y at level 200).

Inductive Unit@{i} : Type@{i} := unit : Unit.

Inductive Void@{i} : Type@{i} :=.

Inductive Prod@{i j} (A : Type@{i}) (B : Type@{j}) : Type@{max(i,j)} :=
  | pair : A -> B -> Prod A B.

Arguments pair {A} {B} a b.

Definition fst@{i j} {A : Type@{i}} {B : Type@{j}} (x : Prod@{i j} A B) : A :=
  match x with pair a b => a end.

Definition snd@{i j} {A : Type@{i}} {B : Type@{j}} (x : Prod@{i j} A B) : B :=
  match x with pair a b => b end.

Inductive Sum@{i j} (A : Type@{i}) (B : Type@{j}) : Type@{max(i,j)} :=
  | left : A -> Sum A B
  | right : B -> Sum A B.

Arguments left {A} {B} a.
Arguments right {A} {B} b.
