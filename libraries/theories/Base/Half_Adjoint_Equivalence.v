(** 等価構造です。 *)

Require Googology_In_Coq.Base.Base.
Require Googology_In_Coq.Base.Product.
Require Googology_In_Coq.Base.Dependent_Sum.
Require Googology_In_Coq.Base.Path.
Require Googology_In_Coq.Base.Pointwise_Path.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を開きます。 *)

Definition Is_Equivalence (A : Type) (B : Type) (f : A -> B) : Type
  :=
    Dependent_Sum.T
    (B -> A)
    (
      fun g =>
        Dependent_Sum.T
          (
            Product.T
              (Pointwise_Path.T (Function.comp g f) Function.id)
              (Pointwise_Path.T (Function.comp f g) Function.id)
          )
          (
            fun psr =>
              match psr with
                Product.pair s r =>
                  forall x : A,
                    Path.T
                      (Pointwise_Path.apply (Pointwise_Path.wisker_L f s) x)
                      (Pointwise_Path.apply (Pointwise_Path.wisker_R f r) x)
              end
          )
    )
.
(* from: originally defined by Hexirp *)

(** 関数 [f] が等価関数であることです。 *)

Definition Equivalence (A : Type) (B : Type) : Type
  := Dependent_Sum.T (A -> B) (fun f => Is_Equivalence A B f)
.
(* from: originally defined by Hexirp *)

(** 型 [A] と型 [B] の間の等価構造です。 *)
