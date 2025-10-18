(** 等価構造です。 *)

Require Googology_In_Coq.Base.Base.
Require Googology_In_Coq.Base.Product.
Require Googology_In_Coq.Base.Dependent_Sum.
Require Googology_In_Coq.Base.Path.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を開きます。 *)

Definition Is_Singleton (A : Type) : Type
  := Dependent_Sum.T A (fun c => forall x : A, Path.T c x)
.
(* from: originally defined by Hexirp *)

(** 型 [A] が単一であることです。 *)

Definition Fiber {A : Type} {B : Type} (f : A -> B) (y : B) : Type
  := Dependent_Sum.T A (fun x => Path.T (f x) y)
.
(* from: originally defined by Hexirp *)

(** [f] の繊維です。 *)

Definition Is_Equivalence (A : Type) (B : Type) (f : A -> B) : Type
  := forall y : B, Is_Singleton (Fiber f y)
.
(* from: originally defined by Hexirp *)

(** 関数 [f] が等価関数であることです。 *)

Definition Equivalence (A : Type) (B : Type) : Type
  := Dependent_Sum.T (A -> B) (fun f => Is_Equivalence A B f)
.
(* from: originally defined by Hexirp *)

(** 型 [A] と型 [B] の間の等価構造です。 *)
