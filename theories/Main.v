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

Inductive DSum@{i j} (A : Type@{i}) (B : A -> Type@{j}) : Type@{max(i,j)} :=
  | dpair : forall a : A, B a -> DSum A B.

Arguments dpair {A} {B} a b.

Definition dfst@{i j} {A : Type@{i}} {B : A -> Type@{j}} (x : DSum@{i j} A B) : A :=
  match x with dpair a b => a end.

Definition dsnd@{i j} {A : Type@{i}} {B : A -> Type@{j}} (x : DSum@{i j} A B) : B (dfst@{i j} x) :=
  match x with dpair a b => b end.

Inductive Path@{i} (A : Type@{i}) (a : A) : A -> Type@{i} :=
  | idpath : Path A a a.

Arguments Path {A} a a'.

Arguments idpath {A} {a}, [A] a.

Definition idmap@{i} {A : Type@{i}} (x : A) : A := x.

Definition const@{i j} {A : Type@{i}} {B : Type@{j}} (x : A) (y : B) : A := x.

Definition comp_f@{i j k} {A : Type@{i}} {B : Type@{j}} {C : Type@{k}} (f : B -> C) (g : A -> B) (x : A) : C := f (g x).

Definition comp_d@{i j k} {A : Type@{i}} {B : Type@{j}} {C : B -> Type@{k}} (f : forall b : B, C b) (g : A -> B) (x : A) : C (g x) := f (g x).

Print comp_d.
