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
    := Dependent_Sum.first A (beta t A B)
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
    := Dependent_Sum.second A (beta t A B)
.
(* from: originally defined by Hexirp *)

(** ウ型のアルファの第二射影関数です。 *)
