(** 点ごとの道です。 *)

Require Googology_In_Coq.Base.Base.
Require Googology_In_Coq.Base.Function.
Require Googology_In_Coq.Base.Path.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を開きます。 *)

Definition T (A : Type) (B : Type)
  : (A -> B) -> (A -> B) -> Type
  :=
    fun (f : A -> B) (g : A -> B) =>
      forall x : A, Path.T (f x) (g x)
.
(* from: originally defined by Hexirp *)

(** 主型です。 *)

Definition to_Function_1 (A : Type) (B : Type)
  :
    forall (f : A -> B) (g : A -> B),
      T A B f g -> Function.T_ A (@Path.T A) B (@Path.T B) f g
.
Proof.
  move=> f g.
  unfold T; unfold Function.T_.
  move=> h.
  move=> x y.
  move=> p.
  refine (let D := fun y : A => Path.T (f x) (g y) in _).
  change (D y).
  refine (Path.trpt p _).
  exact (h x).
Defined.
(* from: originally defined by Hexirp *)

(** [Function.T_] への変換です。 *)

Definition from_Function_1 (A : Type) (B : Type)
  :
    forall (f : A -> B) (g : A -> B),
      Function.T_ A (@Path.T A) B (@Path.T B) f g -> T A B f g
.
Proof.
  move=> f g.
  unfold Function.T_; unfold T.
  move=> h.
  move=> x.
  exact (h x x Path.id).
Defined.
(* from: originally defined by Hexirp *)

(** [Function.T_] からの変換です。 *)

Definition id {A : Type} {B : Type}{f : A -> B}
  : T A B f f
  := fun x : A => Path.id
.
(* from: originally defined by Hexirp *)

(** 点ごとの道の恒等道です。 *)

Definition conc
    {A : Type}
    {B : Type}
    {f : A -> B}
    {g : A -> B}
    {h : A -> B}
  : T A B f g -> T A B g h -> T A B f h
.
Proof.
  unfold T.
  move=> p q.
  move=> x.
  exact (Path.conc (p x) (q x)).
Defined.
(* from: originally defined by Hexirp *)

(** 点ごとの道の合成です。 *)

Definition inv
    {A : Type}
    {B : Type}
    {f : A -> B}
    {g : A -> B}
  : T A B f g -> T A B g f
.
Proof.
  unfold T.
  move=> p.
  move=> x.
  exact (Path.inv (p x)).
Defined.
(* from: originally defined by Hexirp *)

(** 点ごとの道の逆です。 *)

Definition wiskerL
    {A : Type}
    {B : Type}
    {C : Type}
    (f : B -> C)
    {g : A -> B}
    {h : A -> B}
  : T A B g h -> T A C (Function.comp f g) (Function.comp f h)
.
Proof.
  unfold T.
  move=> p.
  move=> x.
  exact (Path.ap f (p x)).
Defined.
(* from: originally defined by Hexirp *)

(** 左からの髭つけです。 *)

Definition wiskerR
    {A : Type}
    {B : Type}
    {C : Type}
    (f : A -> B)
    {g : B -> C}
    {h : B -> C}
  : T B C g h -> T A C (Function.comp g f) (Function.comp h f)
.
Proof.
  unfold T.
  move=> p.
  move=> x.
  exact (p (f x)).
Defined.
(* from: originally defined by Hexirp *)

(** 右からの髭つけです。 *)

Definition wiskerLR
    {A : Type}
    {B : Type}
    {C : Type}
    {D : Type}
    (f_0 : C -> D)
    (f_1 : A -> B)
    {g : B -> C}
    {h : B -> C}
  :
      T B C g h
    ->
      T
        A
        D
        (Function.comp f_0 (Function.comp g f_1))
        (Function.comp f_0 (Function.comp h f_1))
  := fun p : T B C g h => wiskerL f_0 (wiskerR f_1 p)
.
(* from: originally defined by Hexirp *)

(** 左右からの髭つけです。 *)
