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

Definition comp@{i j k} {A : Type@{i}} {B : Type@{j}} {C : Type@{k}} (f : B -> C) (g : A -> B) (x : A) : C := f (g x).

Definition compD@{i j k} {A : Type@{i}} {B : Type@{j}} {C : B -> Type@{k}} (f : forall b : B, C b) (g : A -> B) (x : A) : C (g x) := f (g x).

Definition apply@{i j} {A : Type@{i}} {B : Type@{j}} (f : A -> B) (x : A) : B := f x.

Definition applyD@{i j} {A : Type@{i}} {B : A -> Type@{j}} (f : forall a : A, B a) (x : A) : B x := f x.

Definition absurd@{i j} {A : Type@{i}} (x : Void@{j}) : A :=
  match x with end.

Definition curry@{i j k} {A : Type@{i}} {B : Type@{j}} {C : Type@{k}} (f : Prod@{i j} A B -> C) (x : A) (y : B) : C :=
  f (pair x y).

Definition uncurry@{i j k} {A : Type@{i}} {B : Type@{j}} {C : Type@{k}} (f : A -> B -> C) (x : Prod@{i j} A B) : C :=
  match x with pair a b => f a b end.

Definition inv@{i} {A : Type@{i}} {x y : A} (p : Path@{i} x y) : Path@{i} y x :=
  match p with idpath => idpath end.

Definition conc@{i} {A : Type@{i}} {x y z : A} (p : Path@{i} x y) (q : Path@{i} y z) : Path@{i} x z :=
  match q with idpath => match p with idpath => idpath end end.

Definition ap@{i j} {A : Type@{i}} {B : Type@{j}} (f : A -> B) {x y : A} (p : Path@{i} x y) : Path@{j} (f x) (f y) :=
  match p with idpath => idpath end.

Inductive Bool@{i} : Type@{i} :=
  | false : Bool
  | true : Bool.

Inductive Ordering@{i} : Type@{i} :=
  | les : Ordering
  | eql : Ordering
  | grt : Ordering.

Definition Rel@{i j} (A : Type@{i}) : Type@{max(i,j)} := A -> A -> Bool@{j}.

Inductive Acc@{i j} {A : Type@{i}} (r : Rel@{i j} A) : A -> Type@{max(i,j)} :=
  mkAcc : forall a : A, (forall a' : A, Path@{j} (r a' a) true -> Acc r a') -> Acc r a.

Definition WFd@{i j} {A : Type@{i}} (r : Rel@{i j} A) : Type@{max(i,j)} :=
  forall a : A, Acc@{i j} r a.

Print WFd.
