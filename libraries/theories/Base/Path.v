(** 道の型に関するモジュールです。 *)

(** [match] 式をオープンにしない理由は道の型を定義する方法に複数の種類があるためです。具体的には、基点がある定義や基点がない定義や cubical 風に interval を使う定義などがあります。 *)

Require Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を要求します。 *)

Import Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を開きます。 *)

Private Inductive T (A : Type) (a : A) 
  : A -> Type
  := id : T A a a
.
(* from: originally defined by Hexirp *)

(** 主型です。 *)

Arguments T {A} a a'.

(** [Path] についての暗黙引数を設定します。 *)

Arguments id {A} {a}, [A] a.

(** [id] についての暗黙引数を設定します。 [id] と書いたときは [id _ _] と補われます。 [id a] と書いたときは [idpath _ a] と補われます。 *)

Definition conc {A : Type} {x y z : A}
  : T x y -> T y z -> T x z
  :=
    fun (p : T x y) (q : T y z) =>
      match q with id => match p with id => id end end
.
(* from: originally defined by Hexirp *)

(** 道の結合です。 *)

Definition inv {A : Type} {x y : A}
  : T x y -> T y x
  := fun p : T x y => match p with id => id end
.
(* from: originally defined by Hexirp *)

(** 道の逆です。 *)

Definition trpt {A : Type} {B : A -> Type} {x y : A}
  : T x y -> B x -> B y
  := fun (p : T x y) (u : B x) => match p with id => u end
.
(* from: originally defined by Hexirp *)

(** 道による輸送です。 *)

Definition trptD {A : Type} {x : A} (P : forall y : A, T x y -> Type) {y : A}
  : forall p : T x y, P x id -> P y p
  := fun (p : T x y) (u : P x id) => match p with id => u end
.
(* from: originally defined by Hexirp *)

(** 道による依存型バージョンの輸送です。 *)

Definition ap {A : Type} {B : Type} (f : A -> B) {x y : A}
  : T x y -> T (f x) (f y)
  := fun p : T x y => match p with id => id end
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
  :=
    fun (p : T A B) (u : A) =>
      trptD
        (fun (B_ : Type) (p_ : T A B_) => B_)
        p
        u
.
(* from: originally defined by Hexirp *)

(** 型の変換です。 *)
