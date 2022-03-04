(** ウ型のアルファに関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Dependent_Sum.
Require Googology_In_Coq.W_type_Beta.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Dependent_Sum (Dependent_Sum).
Import Googology_In_Coq.W_type_Beta (W_type_Beta).

(** ライブラリを開きます。 *)

Definition
  W_type_Alpha@{i | }
      (t : forall (A : Type@{i}) (B : A -> Type@{i}), Type@{i})
      (A : Type@{i})
      (B : A -> Type@{i})
    : Type@{i}
    := Dependent_Sum A (W_type_Beta t A B)
.
(* from: originally defined by Hexirp *)

(** ウ型のアルファです。 *)

Definition
  pair@{i | }
      (t : forall (A : Type@{i}) (B : A -> Type@{i}), Type@{i})
      (A : Type@{i})
      (B : A -> Type@{i})
      (a : A)
      (b : W_type_Beta t A B a)
    : W_type_Alpha t A B
    := Dependent_Sum.pair A (W_type_Beta t A B) a b
.
(* from: originally defined by Hexirp *)

(** ウ型のアルファの構築子です。 *)

Definition
  matching@{i | }
      (t : forall (A : Type@{i}) (B : A -> Type@{i}), Type@{i})
      (A : Type@{i})
      (B : A -> Type@{i})
      (P : W_type_Alpha t A B -> Type@{i})
      (
        constructor_pair
          : forall (a : A) (b : W_type_Beta t A B a), P (pair t A B a b)
      )
    : forall x : W_type_Alpha t A B, P x
    := Dependent_Sum.matching A (W_type_Beta t A B) P constructor_pair
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  matching_nodep@{i | }
      (t : forall (A : Type@{i}) (B : A -> Type@{i}), Type@{i})
      (A : Type@{i})
      (B : A -> Type@{i})
      (P : Type@{i})
      (constructor_pair : forall a : A, W_type_Beta t A B a -> P)
    : W_type_Alpha t A B -> P
    := matching t A B (fun x_ : W_type_Alpha t A B => P) constructor_pair
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  first@{i | }
      (t : forall (A : Type@{i}) (B : A -> Type@{i}), Type@{i})
      (A : Type@{i})
      (B : A -> Type@{i})
    : W_type_Alpha t A B -> A
    := matching_nodep t A B A (fun (a : A) (b : W_type_Beta t A B a) => a)
.
(* from: originally defined by Hexirp *)

(** ウ型のアルファの第一射影関数です。 *)

Definition
  second@{i | }
      (t : forall (A : Type@{i}) (B : A -> Type@{i}), Type@{i})
      (A : Type@{i})
      (B : A -> Type@{i})
    : forall x : W_type_Alpha t A B, W_type_Beta t A B (first t A B x)
    :=
      matching
        t
        A
        B
        (fun x_ : W_type_Alpha t A B => W_type_Beta t A B (first t A B x_))
        (fun (a : A) (b : W_type_Beta t A B a) => b)
.
(* from: originally defined by Hexirp *)

(** ウ型のアルファの第二射影関数です。 *)
