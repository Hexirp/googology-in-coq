(** 道に関するモジュールです。 *)

(** [match] 式をオープンにしない理由は、道を定義する方法に複数の種類があるためです。具体的には、基点がある定義や基点がない定義や cubical 風に interval を使う定義などがあります。 *)

Require Googology_In_Coq.Base.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.

(** ライブラリを開きます。 *)

Module Core.

Private Inductive
  Path@{i | } (A : Type@{i}) (a : A) : A -> Type@{i} := id : Path A a a
.
(* from: originally defined by Hexirp *)

Definition
  induction@{i | }
      (A : Type@{i})
      (a : A)
      (P : forall a' : A, Path A a a' -> Type@{i})
      (constructor_id : P a (id A a))
    : forall (a' : A) (x : Path A a a'), P a' x
    :=
      fun (a' : A) (x : Path A a a') =>
        match x as x_ in Path _ _ a'_ return P a'_ x_ with
          id _ _ => constructor_id
        end
.
(* from: originally defined by Hexirp *)

End Core.

Definition
  Path@{i | } {A : Type@{i}} (a : A) (a' : A) : Type@{i} := Core.Path A a a'
.
(* from: originally defined by Hexirp *)

(** 道です。 *)

Definition
  Path_Visible@{i | } (A : Type@{i}) (a : A) (a' : A) : Type@{i}
    := Core.Path A a a'
.
(* from: originally defined by Hexirp *)

(** 引数が明示的な [Path] です。 *)

Definition id@{i | } (A : Type@{i}) (a : A) : Path a a := Core.id A a.
(* from: originally defined by Hexirp *)

(** 恒等道です。 *)

Arguments id {A} {a}, [A] a.

(** [id] についての暗黙引数を設定します。 [id] と書いたときは [@id _ _] と補われます。 [id a] と書いたときは [@id _ a] と補われます。 *)

Definition
  induction@{i | }
      (A : Type@{i})
      (a : A)
      (P : forall a' : A, Path a a' -> Type@{i})
      (constructor_id : P a id)
    : forall (a' : A) (x : Path a a'), P a' x
    := Core.induction A a P constructor_id
.
(* from: originally defined by Hexirp *)

(** 基点付き道帰納法です。 *)

Definition
  jay@{i | }
      (A : Type@{i})
      (P : forall (a : A) (a' : A), Path a a' -> Type@{i})
      (constructor_id : forall a : A, P a a id)
    : forall (a : A) (a' : A) (x : Path a a'), P a a' x
    :=
      fun a : A =>
        induction
          A
          a
          (fun (a'_ : A) (x_ : Path a a'_) => P a a'_ x_)
          (constructor_id a)
.
(* from: originally defined by Hexirp *)

(** マーティン・レーフの J 規則です。 *)

Definition
  trpt@{i | } {A : Type@{i}} {B : A -> Type@{i}} {x y : A}
    : Path x y -> B x -> B y
    :=
      fun (p : Path x y) (u : B x) =>
        induction A x (fun (y_ : A) (_ : Path x y_) => B y_) u y p
.
(* from: originally defined by Hexirp *)

(** 輸送です。 *)

Definition
  trpt_visible@{i | } (A : Type@{i}) (B : A -> Type@{i}) {x y : A}
    : Path x y -> B x -> B y
    :=
      fun (p : Path x y) (u : B x) =>
        induction A x (fun (y_ : A) (_ : Path x y_) => B y_) u y p
.
(* from: originally defined by Hexirp *)

(** 引数が明示的な [trpt] です。 *)

Definition
  trpt_dependent@{i | }
      {A : Type@{i}}
      {x : A}
      (B : forall y : A, Path x y -> Type@{i})
      {y : A}
    : forall p : Path x y, B x id -> B y p
    :=
      fun (p : Path x y) (u : B x id) =>
        induction A x (fun (y_ : A) (p_ : Path x y_) => B y_ p_) u y p
.
(* from: originally defined by Hexirp *)

(** 依存型に対応した [trpt] です。 *)

Definition
  conc@{i | } {A : Type@{i}} {x y z : A} : Path x y -> Path y z -> Path x z
    := fun (p : Path x y) (q : Path y z) => trpt q (trpt p id)
.
(* from: originally defined by Hexirp *)

(** 道の結合です。 *)

Definition
  inv@{i | } {A : Type@{i}} {x y : A} : Path x y -> Path y x
    := fun p : Path x y => trpt_visible A (fun y_ => Path y_ x) p id
.
(* from: originally defined by Hexirp *)

(** 道の逆です。 *)

Definition
  ap@{i | } {A : Type@{i}} {B : Type@{i}} (f : A -> B) {x y : A}
    : Path x y -> Path (f x) (f y)
    := fun p : Path x y => trpt_visible A (fun y_ => Path (f x) (f y_)) p id
.
(* from: originally defined by Hexirp *)

(** 道への適用です。 *)

Definition
  conv@{i | } {A : Type@{i}} {x y z : A} : Path x y -> Path x z -> Path y z
    := fun (p : Path x y) (q : Path x z) => conc (inv p) q
.
(* from: originally defined by Hexirp *)

(** 道の結合と逆です。 *)

Definition
  trpv@{i | } {A : Type@{i}} {B : A -> Type@{i}} {x y : A}
    : Path x y -> B y -> B x
    := fun (p : Path x y) (u : B y) => trpt (inv p) u
.
(* from: originally defined by Hexirp *)

(** 道による輸送と逆です。 *)
