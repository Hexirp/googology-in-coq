(** 道に関するモジュールです。 *)

(** [match] 式をオープンにしない理由は、道を定義する方法に複数の種類があるためです。具体的には、基点がある定義や基点がない定義や cubical 風に interval を使う定義などがあります。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Function.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Function (Function).

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
      (P : forall a' : A, Path@{i} A a a' -> Type@{i})
      (constructor_id : P a (id A a))
    : forall (a' : A) (x : Path@{i} A a a'), P a' x
    :=
      fun (a' : A) (x : Path@{i} A a a') =>
        match x as x_ in Path _ _ a'_ return P a'_ x_ with
          id _ _ => constructor_id
        end
.
(* from: originally defined by Hexirp *)

End Core.

(** 道の定義を隠蔽します。 *)

Definition
  Path@{i | } (A : Type@{i}) (a : A) (a' : A) : Type@{i}
    := Core.Path@{i} A a a'
.
(* from: originally defined by Hexirp *)

(** 道です。 *)

Definition id@{i | } (A : Type@{i}) (a : A) : Path A a a := Core.id A a.
(* from: originally defined by Hexirp *)

Definition
  induction@{i | }
      (A : Type@{i})
      (a : A)
      (P : forall a' : A, Path@{i} A a a' -> Type@{i})
      (constructor_id : P a (id A a))
    : forall (a' : A) (x : Path@{i} A a a'), P a' x
    := Core.induction A a P constructor_id
.
(* from: originally defined by Hexirp *)

(** 基点付き道帰納法です。 *)

Definition
  jay@{i | }
      (A : Type@{i})
      (P : forall (a : A) (a' : A), Path@{i} A a a' -> Type@{i})
      (constructor_id : forall a : A, P a a (id A a))
    : forall (a : A) (a' : A) (x : Path@{i} A a a'), P a a' x
    :=
      fun a : A =>
        induction
          A
          a
          (fun (a'_ : A) (x_ : Path@{i} A a a'_) => P a a'_ x_)
          (constructor_id a)
.
(* from: originally defined by Hexirp *)

(** マーティン・レーフの J 規則です。 *)

Definition
  trpt@{i | } (A : Type@{i}) (x : A) (y : A) (B : A -> Type@{i})
    : Path@{i} A x y -> B x -> B y
    :=
      fun (p : Path@{i} A x y) (u : B x) =>
        induction A x (fun (y_ : A) (p_ : Path@{i} A x y_) => B y_) u y p
.
(* from: originally defined by Hexirp *)

(** 輸送です。 *)

Definition
  trpt_dep@{i | }
      (A : Type@{i})
      (x : A)
      (y : A)
      (B : forall y : A, Path@{i} A x y -> Type@{i})
    : forall p : Path A x y, B x (id A x) -> B y p
    :=
      fun (p : Path@{i} A x y) (u : B x (id A x)) =>
        induction A x (fun (y_ : A) (p_ : Path@{i} A x y_) => B y_ p_) u y p
.
(* from: originally defined by Hexirp *)

(** 依存型に対応した [trpt] です。 *)

Definition
  conc@{i | } (A : Type@{i}) (x : A) (y : A) (z : A)
    : Path@{i} A x y -> Path@{i} A y z -> Path@{i} A x z
    :=
      fun (p : Path@{i} A x y) (q : Path@{i} A y z) =>
        trpt A y z (Path@{i} A x) q (trpt A x y (Path@{i} A x) p (id A x))
.
(* from: originally defined by Hexirp *)

(** 道の結合です。 *)

Definition
  inv@{i | } (A : Type@{i}) (x : A) (y : A)
    : Path@{i} A x y -> Path@{i} A y x
    :=
      fun p : Path@{i} A x y =>
        trpt A x y (fun y_ => Path@{i} A y_ x) p (id A x)
.
(* from: originally defined by Hexirp *)

(** 道の逆です。 *)

Definition
  ap@{i | }
      (A : Type@{i})
      (B : Type@{i})
      (f : Function@{i} A B)
      (x : A)
      (y : A)
    :
        Path@{i} A x y
      ->
        Path@{i} B (Function.apply A B f x) (Function.apply A B f y)
    :=
      fun p : Path@{i} A x y =>
        trpt
          A
          x
          y
          (
            fun y_ =>
              Path@{i} B (Function.apply A B f x) (Function.apply A B f y_)
          )
          p
          (id B (Function.apply A B f x))
.
(* from: originally defined by Hexirp *)

(** 道への適用です。 *)

Definition
  conv@{i | } (A : Type@{i}) (x : A) (y : A) (z : A)
    : Path@{i} A x y -> Path@{i} A x z -> Path@{i} A y z
    :=
      fun (p : Path@{i} A x y) (q : Path@{i} A x z) =>
        conc A y x z (inv A x y p) q
.
(* from: originally defined by Hexirp *)

(** 道の結合と逆です。 *)

Definition
  trpv@{i | } (A : Type@{i}) (x : A) (y : A) (B : A -> Type@{i})
    : Path@{i} A x y -> B y -> B x
    := fun (p : Path@{i} A x y) (u : B y) => trpt A y x B (inv A x y p) u
.
(* from: originally defined by Hexirp *)

(** 道による輸送と逆です。 *)

Definition
  function_abstract_apply@{i | }
      (A : Type@{i})
      (B : Type@{i})
      (x : Function@{i} A B)
    :
      Path@{i}
        (Function@{i} A B)
        (Function.abstract A B (Function.apply A B x))
        x
    :=
      Function.matching
        A
        B
        (
          fun x_ : Function@{i} A B =>
            Path@{i}
              (Function@{i} A B)
              (Function.abstract A B (Function.apply A B x_))
              x_
        )
        (fun x_v : A -> B => id (Function@{i} A B) (Function.wrap A B x_v))
        x
.
(* from: originally defined by Hexirp *)

(** [Function] の η 変換です。 *)
