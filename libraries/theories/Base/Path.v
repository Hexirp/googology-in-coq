(** 道の型に関するモジュールです。 *)

(** [match] 式をオープンにしない理由は道の型を定義する方法に複数の種類があるためです。具体的には、基点がある定義や基点がない定義や cubical 風に interval を使う定義などがあります。 *)

Require Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を要求します。 *)

Import Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を開きます。 *)

Module Internal.

Private Inductive T (A : Type) (a : A) 
  : A -> Type
  := id : T A a a
.
(* from: originally defined by Hexirp *)

(** 主型です。 *)

Definition induction
    (A : Type)
    (a : A)
    (P : forall b : A, T A a b -> Type)
    (construct_id : P a (id A a))
  : forall (b : A) (x : T A a b), P b x
  :=
    fun (b : A) (x : T A a b) =>
      match x as x_ in T _ _ b_ return P b_ x_ with id _ _ => construct_id end
.
(* from: originally defined by Hexirp *)

(** 道の帰納法です。 J axiom や J rule などとも呼ばれます。 *)

End Internal.

Definition T (A : Type) (a : A) (a' : A) : Type := Internal.T A a a'.
(* from: originally defined by Hexirp *)

(** 主型です。 *)

Arguments T {A} a a'.

(** [T] についての暗黙引数を設定します。 *)

Definition id (A : Type) (a : A) : T a a := Internal.id A a.
(* from: originally defined by Hexirp *)

(** 恒等道です。 *)

Arguments id {A} {a}, [A] a.

(** [id] についての暗黙引数を設定します。 [id] と書いたときは [@id _ _] と補われます。 [id a] と書いたときは [@id _ a] と補われます。 *)

Definition induction
    (A : Type)
    (a : A)
    (P : forall b : A, T a b -> Type)
    (construct_id : P a id)
  : forall (b : A) (x : T a b), P b x
  := Internal.induction A a P construct_id
.
(* from: originally defined by Hexirp *)

(** 道の帰納法です。 J axiom や J rule などとも呼ばれます。 *)

Definition trpt {A : Type} {B : A -> Type} {x y : A}
  : T x y -> B x -> B y
  :=
    fun (p : T x y) (u : B x) =>
      induction A x (fun (y_ : A) (_ : T x y_) => B y_) u y p
.
(* from: originally defined by Hexirp *)

(** 道による輸送です。 *)

Definition trpt_visible {A : Type} (B : A -> Type) {x y : A}
: T x y -> B x -> B y
:=
  fun (p : T x y) (u : B x) =>
    induction A x (fun (y_ : A) (_ : T x y_) => B y_) u y p
.
(* from: originally defined by Hexirp *)

(** 引数が明示的な [trpt] です。 *)

Definition trptD {A : Type} {x : A} (B : forall y : A, T x y -> Type) {y : A}
  : forall p : T x y, B x id -> B y p
  :=
    fun (p : T x y) (u : B x id) =>
      induction A x (fun (y_ : A) (p_ : T x y_) => B y_ p_) u y p
.
(* from: originally defined by Hexirp *)

(** 依存型に対応した [trpt] です。 *)

Definition conc {A : Type} {x y z : A}
  : T x y -> T y z -> T x z
  := fun (p : T x y) (q : T y z) => trpt q (trpt p id)
.
(* from: originally defined by Hexirp *)

(** 道の結合です。 *)

Definition inv {A : Type} {x y : A}
  : T x y -> T y x
  := fun p : T x y => trpt_visible (fun y_ : A => T y_ x) p id
.
(* from: originally defined by Hexirp *)

(** 道の逆です。 *)

Definition ap {A : Type} {B : Type} (f : A -> B) {x y : A}
  : T x y -> T (f x) (f y)
  := fun p : T x y => trpt_visible (fun y_ : A => T (f x) (f y_)) p id
.
(* from: originally defined by Hexirp *)

(** 道への適用です。 *)

Definition conv {A : Type} {x y z : A}
  : T x y -> T x z -> T y z
  := fun (p : T x y) (q : T x z) => conc (inv p) q
.
(* from: originally defined by Hexirp *)

(** 道の結合と逆です。 *)

Definition trpv {A : Type} {B : A -> Type} {x y : A}
  : T x y -> B y -> B x
  := fun (p : T x y) (u : B y) => trpt (inv p) u
.
(* from: originally defined by Hexirp *)

(** 道による輸送と逆です。 *)

Definition coerce {A : Type} {B : Type}
  : T A B -> A -> B
  := fun (p : T A B) (u : A) => trpt_visible (fun B_ : Type => B_) p u
.
(* from: originally defined by Hexirp *)

(** 型の変換です。 *)
