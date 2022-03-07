(** 直積型に関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Dependent_Sum.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Dependent_Sum (Dependent_Sum).

(** ライブラリを開きます。 *)

Inductive
  Product@{i | } (A : Type@{i}) (B : Type@{i}) : Type@{i}
    := wrap : Dependent_Sum@{i} A (fun a : A => B) -> Product A B
.
(* from: originally defined by Hexirp *)

(** 直積型です。 *)

Definition
  unwrap@{i | } (A : Type@{i}) (B : Type@{i})
    : Product@{i} A B -> Dependent_Sum@{i} A (fun a : A => B)
    := fun x : Product@{i} A B => match x with wrap _ _ x_v => x_v end
.
(* from: originally defined by Hexirp *)

(** 直積型です。 *)

Definition
  pair@{i | } (A : Type@{i}) (B : Type@{i}) : A -> B -> Product A B
    :=
      fun (x_1 : A) (x_2 : B) =>
        wrap A B (Dependent_Sum.pair A (fun a : A => B) x_1 x_2)
.
(* from: originally defined by Hexirp *)

(** ペアリング関数です。 *)

Definition
  matching@{i | }
      (A : Type@{i})
      (B : Type@{i})
      (P : Product A B -> Type@{i})
      (constructor_pair : forall (x_1 : A) (x_2 : B), P (pair A B x_1 x_2))
    : forall x : Product A B, P x
    :=
      fun x : Product A B =>
        match x as x_ return P x_ with
          wrap _ _ x_v =>
            Dependent_Sum.matching
              A
              (fun a : A => B)
              (
                fun x_v_ : Dependent_Sum A (fun a : A => B) =>
                  P (wrap A B x_v_)
              )
              constructor_pair
              x_v
        end
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  matching_nodep@{i | }
      (A : Type@{i})
      (B : Type@{i})
      (P : Type@{i})
      (constructor_pair : A -> B -> P)
    : Product A B -> P
    := matching A B (fun x_ : Product A B => P) constructor_pair
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  first@{i | } (A : Type@{i}) (B : Type@{i}) : Product A B -> A
    := matching_nodep A B A (fun (a : A) (b : B) => a)
.
(* from: originally defined by Hexirp *)

(** 直積型の第一射影関数です。 *)

Definition
  second@{i | } (A : Type@{i}) (B : Type@{i}) : Product A B -> B
    := matching_nodep A B B (fun (a : A) (b : B) => b)
.
(* from: originally defined by Hexirp *)

(** 直積型の第二射影関数です。 *)

Definition
  comatching_nodep@{i | }
      (A : Type@{i})
      (B : Type@{i})
      (P : Type@{i})
      (destructor_first : P -> A)
      (destructor_second : P -> B)
    : P -> Product A B
    := fun x : P => pair A B (destructor_first x) (destructor_second x)
.
(* from: originally defined by Hexirp *)

(** 余場合分けです。 *)

Definition
  curry@{i | } (A : Type@{i}) (B : Type@{i}) (C : Type@{i})
    : (Product A B -> C) -> A -> B -> C
    := fun (f : Product A B -> C) (x : A) (y : B) => f (pair A B x y)
.
(* from: originally defined by Hexirp *)

(** 関数のカリー化です。 *)

Definition
  uncurry@{i | } (A : Type@{i}) (B : Type@{i}) (C : Type@{i})
    : (A -> B -> C) -> Product A B -> C
    :=
      fun (f : A -> B -> C) (x : Product A B) => f (first A B x) (second A B x)
.
(* from: originally defined by Hexirp *)

(** 関数の非カリー化です。 *)

Definition
  map@{i | }
      (A : Type@{i})
      (B : Type@{i})
      (C : Type@{i})
      (D : Type@{i})
      (f : A -> C)
      (g : B -> D)
    : Product@{i} A B -> Product@{i} C D
    :=
      fun x : Product@{i} A B => pair C D (f (first A B x)) (g (second A B x))
.
(* from: originally defined by Hexirp *)

(** 直積型の写像です。 *)
