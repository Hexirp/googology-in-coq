(** 依存直和型に関するモジュールです。 *)

Require Googology_In_Coq.Base.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.

(** ライブラリを開きます。 *)

Inductive
  Dependent_Sum@{i | } (A : Type@{i}) (B : A -> Type@{i}) : Type@{i}
    := pair : forall a : A, B a -> Dependent_Sum A B
.
(* from: originally defined by Hexirp *)

(** 依存直和型です。 *)

Definition
  matching@{i | }
      (A : Type@{i})
      (B : A -> Type@{i})
      (P : Dependent_Sum A B -> Type@{i})
      (constructor_pair : forall (a : A) (b : B a), P (pair A B a b))
    : forall x : Dependent_Sum A B, P x
    :=
      fun x : Dependent_Sum A B =>
        match x as x_ return P x_ with
          pair _ _ a b => constructor_pair a b
        end
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  matching_nodep@{i | }
      (A : Type@{i})
      (B : A -> Type@{i})
      (P : Type@{i})
      (constructor_pair : forall a : A, B a -> P)
    : Dependent_Sum A B -> P
    := matching A B (fun x_ : Dependent_Sum A B => P) constructor_pair
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  first@{i | } (A : Type@{i}) (B : A -> Type@{i}) : Dependent_Sum A B -> A
    := matching_nodep A B A (fun (a : A) (b : B a) => a)
.
(* from: originally defined by Hexirp *)

(** 依存直和型の第一射影関数です。 *)

Definition
  second@{i | } (A : Type@{i}) (B : A -> Type@{i})
    : forall x : Dependent_Sum A B, B (first A B x)
    :=
      matching
        A
        B
        (fun x_ : Dependent_Sum A B => B (first x_))
        (fun (a : A) (b : B a) => b)
.
(* from: originally defined by Hexirp *)

(** 依存直和型の第二射影関数です。 *)

Definition
  map@{i | }
      (A : Type@{i})
      (B : A -> Type@{i})
      (C : Type@{i})
      (D : C -> Type@{i})
      (f : A -> C)
      (g : forall x : A, B x -> D (f x))
    : Dependent_Sum@{i} A B -> Dependent_Sum@{i} C D
    :=
      fun x : Dependent_Sum@{i} A B =>
        pair C D (f (first A B x)) (g (first A B x) (second A B x))
.
(* from: originally defined by Hexirp *)

(** 依存直和型の写像です。 *)
