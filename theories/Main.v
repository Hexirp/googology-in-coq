Unset Elimination Schemes.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Set Printing Universes.

Notation "x -> y" := (forall (_ : x), y) (at level 99, right associativity, y at level 200).

Inductive Unit@{i} : Type@{i} := unit : Unit.

Inductive Void@{i} : Type@{i} :=.

Inductive Prod@{i j} (A : Type@{i}) (B : Type@{j}) : Type@{max(i,j)}
  := pair : A -> B -> Prod A B.

Arguments pair {A} {B} a b.

Definition fst@{i j} {A : Type@{i}} {B : Type@{j}} (x : Prod@{i j} A B) : A
  := match x with pair a b => a end.

Definition snd@{i j} {A : Type@{i}} {B : Type@{j}} (x : Prod@{i j} A B) : B
  := match x with pair a b => b end.

Inductive Sum@{i j} (A : Type@{i}) (B : Type@{j}) : Type@{max(i,j)}
  := left : A -> Sum A B | right : B -> Sum A B.

Arguments left {A} {B} a.
Arguments right {A} {B} b.

Inductive DSum@{i j} (A : Type@{i}) (B : A -> Type@{j}) : Type@{max(i,j)}
  := dpair : forall a : A, B a -> DSum A B.

Arguments dpair {A} {B} a b.

Definition dfst@{i j} {A : Type@{i}} {B : A -> Type@{j}} (x : DSum@{i j} A B) : A
  := match x with dpair a b => a end.

Definition dsnd@{i j} {A : Type@{i}} {B : A -> Type@{j}} (x : DSum@{i j} A B) : B (dfst@{i j} x)
  := match x with dpair a b => b end.

Inductive Path@{i} (A : Type@{i}) (a : A) : A -> Type@{i}
  := idpath : Path A a a.

Arguments Path {A} a a'.

Arguments idpath {A} {a}, [A] a.

Definition idmap@{i} {A : Type@{i}} (x : A) : A := x.

Definition const@{i j} {A : Type@{i}} {B : Type@{j}} (x : A) (y : B) : A := x.

Definition comp@{i j k} {A : Type@{i}} {B : Type@{j}} {C : Type@{k}} (f : B -> C) (g : A -> B) (x : A) : C := f (g x).

Definition compD@{i j k} {A : Type@{i}} {B : Type@{j}} {C : B -> Type@{k}} (f : forall b : B, C b) (g : A -> B) (x : A) : C (g x) := f (g x).

Definition apply@{i j} {A : Type@{i}} {B : Type@{j}} (f : A -> B) (x : A) : B := f x.

Definition applyD@{i j} {A : Type@{i}} {B : A -> Type@{j}} (f : forall a : A, B a) (x : A) : B x := f x.

Definition absurd@{i j} {A : Type@{i}} (x : Void@{j}) : A
  := match x with end.

Definition curry@{i j k} {A : Type@{i}} {B : Type@{j}} {C : Type@{k}} (f : Prod@{i j} A B -> C) (x : A) (y : B) : C
  := f (pair x y).

Definition uncurry@{i j k} {A : Type@{i}} {B : Type@{j}} {C : Type@{k}} (f : A -> B -> C) (x : Prod@{i j} A B) : C
  := match x with pair a b => f a b end.

Definition inv@{i} {A : Type@{i}} {x y : A} (p : Path@{i} x y) : Path@{i} y x
  := match p with idpath => idpath end.

Definition conc@{i} {A : Type@{i}} {x y z : A} (p : Path@{i} x y) (q : Path@{i} y z) : Path@{i} x z
  := match q with idpath => match p with idpath => idpath end end.

Definition trpt@{i j} {A : Type@{i}} {B : A -> Type@{j}} {x y : A} (p : Path@{i} x y) (u : B x) : B y
  := match p with idpath => u end.

Definition ap@{i j} {A : Type@{i}} {B : Type@{j}} (f : A -> B) {x y : A} (p : Path@{i} x y) : Path@{j} (f x) (f y)
  := match p with idpath => idpath end.

Inductive Bool@{i} : Type@{i}
  := false : Bool | true : Bool.

Inductive Ordering@{i} : Type@{i}
  := les : Ordering | eql : Ordering | grt : Ordering.

Definition Rel@{i j} (A : Type@{i}) : Type@{max(i,j)} := A -> A -> Bool@{j}.

Inductive Acc@{i j} {A : Type@{i}} (r : Rel@{i j} A) : A -> Type@{max(i,j)}
  := mkAcc : forall a : A, (forall a' : A, Path@{j} (r a' a) true -> Acc r a') -> Acc r a.

Definition WFd@{i j} {A : Type@{i}} (r : Rel@{i j} A) : Type@{max(i,j)}
  := forall a : A, Acc@{i j} r a.

Definition Ord@{i j} (A : Type@{i}) : Type@{max(i,j)} := A -> A -> Ordering@{j}.

Definition fOrdToRef@{i j k} {A : Type@{i}} (ord : Ord@{i j} A) : Rel@{i k} A
  := fun x y : A => match ord x y with les => true | eql => false | grt => false end.

Definition OrdRfl@{i j} {A : Type@{i}} (ord : Ord@{i j} A) : Type@{max(i,j)}
  := forall x : A, Path@{j} (ord x x) eql.

Definition OrdSym@{i j} {A : Type@{i}} (ord : Ord@{i j} A) : Type@{max(i,j)}
  := forall x y : A,
    Prod@{j j}
      (Path@{j} (ord x y) les -> Path@{j} (ord y x) grt)
      (Path@{j} (ord y x) grt -> Path@{j} (ord x y) les).

Inductive OrdAcc@{i j} {A : Type@{i}} (r : Ord@{i j} A) : A -> Type@{max(i,j)}
  := mkOrdAcc : forall a : A, (forall a' : A, Path@{j} (r a' a) les -> OrdAcc r a') -> OrdAcc r a.

Definition OrdWFd@{i j} {A : Type@{i}} (r : Ord@{i j} A) : Type@{max(i,j)}
  := forall a : A, OrdAcc@{i j} r a.

Inductive Nat@{i} : Type@{i}
  := zero : Nat | succ : Nat -> Nat.

Definition natOrd@{i j} : Ord@{i j} Nat@{i}
  := fix r (x y : Nat@{i}) {struct x} : Ordering@{j}
    := match x, y with
      | zero, zero => eql
      | zero, succ yp => les
      | succ xp, zero => grt
      | succ xp, succ yp => r xp yp
    end.

Definition p_U_V@{i i' | i < i'} (p : Path@{i'} Unit@{i} Void@{i}) : Void@{i}
  := match p with idpath => unit@{i} end.

Declare ML Module "ltac_plugin" .
Set Default Proof Mode "Classic" .

Definition p_natOrd_m_O_les@{i j k k' | k < k'}
  {m : Nat@{i}} (p : Path@{j} (natOrd@{i j} m zero@{i}) les@{j})
  : Void@{k}.
Proof.
  refine (let D := ?[D] : Ordering@{j} -> Type@{k} in _).
  [D]: {
    refine (fun x : Ordering@{j} => _).
    exact (match x return Type@{k} with les => Void@{k} | eql => Unit@{k} | grt => Unit@{k} end).
  }
  refine (let d := ?[d] : Path@{j} (natOrd@{i j} m zero@{i}) les@{j} -> Void@{k} in _).
  [d]: {
    refine (match m as m' return Path@{j} (natOrd@{i j} m' zero@{i}) les@{j} -> Void@{k} with zero => _ | succ mp => _ end).
    {
      refine (fun p => _).
      refine (p_U_V@{k k'} _).
      exact (ap@{j k'} D p).
    }
    {
      refine (fun p => _).
      refine (p_U_V@{k k'} _).
      exact (ap@{j k'} D p).
    }
  }
  exact (d p).
Defined.

Print p_natOrd_m_O_les.

Definition p_natOrd_m_S_n_les@{i j k k' | k < k'}
  {m n : Nat@{i}} (p : Path@{j} (natOrd@{i j} m (succ@{i} n)) les@{j})
  : Sum@{j j} (Path@{j} (natOrd@{i j} m n) eql@{j}) (Path@{j} (natOrd@{i j} m n) les@{j}).
Proof.
  refine (
    let r
      := ?[r]
        : forall m n : Nat@{i},
          Path@{j} (natOrd@{i j} m (succ@{i} n)) les@{j} -> Sum@{j j} (Path@{j} (natOrd@{i j} m n) eql@{j}) (Path@{j} (natOrd@{i j} m n) les@{j})
      in _).
  [r]: {
    refine (
      fix r (m n : Nat@{i}) {struct m}
        : Path@{j} (natOrd@{i j} m (succ@{i} n)) les@{j} -> Sum@{j j} (Path@{j} (natOrd@{i j} m n) eql@{j}) (Path@{j} (natOrd@{i j} m n) les@{j})
        := _).
    refine (
      match m, n with
        | zero, zero => _
        | zero, succ np => _
        | succ mp, zero => _
        | succ mp, succ np => _
      end).
    {
      refine (fun p => _).
      refine (left@{j j} _).
      exact idpath@{j}.
    }
    {
      refine (fun p => _).
      refine (right@{j j} _).
      exact idpath@{j}.
    }
    {
      refine (fun p => _).
      refine (absurd@{j k} _).
      refine (p_natOrd_m_O_les@{i j k k'} (m := mp) _).
      exact p.
    }
    {
      refine (fun p => _).
      refine (r mp np _).
      exact p.
    }
  }
  refine (r m n _).
  exact p.
Defined.

Print p_natOrd_m_S_n_les.

Definition p_natOrd_O_S_n_eql@{i j k k' | k < k'}
  {n : Nat@{i}} (p : Path@{j} (natOrd@{i j} zero@{i} (succ@{i} n)) eql@{j})
  : Void@{k}.
Proof.
  refine (let D := ?[D] : Ordering@{j} -> Type@{k} in _).
  [D]: {
    refine (fun x => _).
    exact (match x with les => Unit@{k} | eql => Void@{k} | grt => Unit@{k} end).
  }
  refine (let d := ?[d] : Path@{j} (natOrd@{i j} zero@{i} (succ@{i} n)) eql@{j} -> Void@{k} in _).
Admitted.

Definition p_natOrd_m_n_eql@{i j} {m n : Nat@{i}} (p : Path@{j} (natOrd@{i j} m n) eql) : Path@{i} m n.
Proof.
  refine (let r := ?[r] : forall m n : Nat@{i}, Path@{j} (natOrd@{i j} m n) eql@{j} -> Path@{i} m n in _).
  [r]: {
    refine (fix r (m n : Nat@{i}) {struct m} : Path@{j} (natOrd@{i j} m n) eql@{j} -> Path@{i} m n := _).
    refine (
      match m, n with
        | zero, zero => _
        | zero, succ np => _
        | succ mp, zero => _
        | succ mp, succ np => _
      end).
    {
      refine (fun p => _).
      exact idpath@{i}.
    }
    {
      admit.
    }
    {
      admit.
    }
    {
      refine (fun p => _).
      refine (ap@{i i} succ@{i} _).
      refine (r mp np _).
      exact p.
    }
  }
Admitted.

Definition WFd_natOrd@{i j k k' | k < k'} : OrdWFd@{i j} natOrd@{i j} :=
  fix r (x : Nat@{i}) {struct x} : OrdAcc@{i j} natOrd@{i j} x
    := match x with
      | zero => mkOrdAcc@{i j} natOrd@{i j} zero@{i} (fun x' o_x'_x =>
        absurd@{j k} (natOrd_m_O@{i j k k'} o_x'_x))
      | succ xp => mkOrdAcc@{i j} natOrd@{i j} (succ@{i} xp) (fun x' o_x'_x =>
        match natOrd_m_S_n@{i j k k'} o_x'_x with
          | left p_x'_xp => trpt@{i j} (inv@{i} (natOrd_m_n@{i j} p_x'_xp)) (r xp)
          | right o_x'_xp => let D
            := match r xp in OrdAcc _ xp' return Path@{i} xp xp' -> OrdAcc@{i j} natOrd@{i j} x' with
              | mkOrdAcc _ xp' ds_r_xp' => fun p => ds_r_xp' x' (trpt@{i j} p o_x'_xp)
            end
            in D idpath@{j}
        end)
    end.
