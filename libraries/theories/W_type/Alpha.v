(** ウ型のアルファに関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Dependent_Sum.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Dependent_Sum (Dependent_Sum).

(** ライブラリを開きます。 *)

Definition
  Alpha@{i | }
      (
        beta
          :
            forall
              t : forall A : Type@{i}, (A -> Type@{i}) -> Type@{i}
            ,
            forall
              (A : Type@{i})
              (B : A -> Type@{i})
            ,
              A -> Type@{i}
      )
      (t : forall (A : Type@{i}) (B : A -> Type@{i}), Type@{i})
      (A : Type@{i})
      (B : A -> Type@{i})
    : Type@{i}
    := Dependent_Sum A (beta t A B)
.
(* from: originally defined by Hexirp *)

(** ウ型のアルファです。 *)

Definition
  pair@{i | }
      (
        beta
          :
            forall
              t : forall A : Type@{i}, (A -> Type@{i}) -> Type@{i}
            ,
            forall
              (A : Type@{i})
              (B : A -> Type@{i})
            ,
              A -> Type@{i}
      )
      (t : forall (A : Type@{i}) (B : A -> Type@{i}), Type@{i})
      (A : Type@{i})
      (B : A -> Type@{i})
      (a : A)
      (b : beta t A B a)
    : Alpha beta t A B
    := Dependent_Sum.pair A (beta t A B) a b
.
(* from: originally defined by Hexirp *)

(** ウ型のアルファの構築子です。 *)

Definition
  matching@{i | }
      (
        beta
          :
            forall
              t : forall A : Type@{i}, (A -> Type@{i}) -> Type@{i}
            ,
            forall
              (A : Type@{i})
              (B : A -> Type@{i})
            ,
              A -> Type@{i}
      )
      (t : forall (A : Type@{i}) (B : A -> Type@{i}), Type@{i})
      (A : Type@{i})
      (B : A -> Type@{i})
      (P : Alpha beta t A B -> Type@{i})
      (
        constructor_pair
          : forall (a : A) (b : beta t A B a), P (pair beta t A B a b)
      )
    : forall x : Alpha beta t A B, P x
    := Dependent_Sum.matching A (beta t A B) P constructor_pair
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  matching_nodep@{i | }
      (
        beta
          :
            forall
              t : forall A : Type@{i}, (A -> Type@{i}) -> Type@{i}
            ,
            forall
              (A : Type@{i})
              (B : A -> Type@{i})
            ,
              A -> Type@{i}
      )
      (t : forall (A : Type@{i}) (B : A -> Type@{i}), Type@{i})
      (A : Type@{i})
      (B : A -> Type@{i})
      (P : Type@{i})
      (constructor_pair : forall a : A, beta t A B a -> P)
    : Alpha beta t A B -> P
    := matching beta t A B (fun x_ : Alpha beta t A B => P) constructor_pair
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  first@{i | }
      (
        beta
          :
            forall
              t : forall A : Type@{i}, (A -> Type@{i}) -> Type@{i}
            ,
            forall
              (A : Type@{i})
              (B : A -> Type@{i})
            ,
              A -> Type@{i}
      )
      (t : forall (A : Type@{i}) (B : A -> Type@{i}), Type@{i})
      (A : Type@{i})
      (B : A -> Type@{i})
    : Alpha beta t A B -> A
    := matching_nodep beta t A B A (fun (a : A) (b : beta t A B a) => a)
.
(* from: originally defined by Hexirp *)

(** ウ型のアルファの第一射影関数です。 *)

Definition
  second@{i | }
      (
        beta
          :
            forall
              t : forall A : Type@{i}, (A -> Type@{i}) -> Type@{i}
            ,
            forall
              (A : Type@{i})
              (B : A -> Type@{i})
            ,
              A -> Type@{i}
      )
      (t : forall (A : Type@{i}) (B : A -> Type@{i}), Type@{i})
      (A : Type@{i})
      (B : A -> Type@{i})
    : forall x : Alpha beta t A B, beta t A B (first beta t A B x)
    :=
      matching
        beta
        t
        A
        B
        (fun x_ : Alpha beta t A B => B (first beta t A B x_))
        (fun (a : A) (b : beta t A B a) => b)
.
(* from: originally defined by Hexirp *)

(** ウ型のアルファの第二射影関数です。 *)
