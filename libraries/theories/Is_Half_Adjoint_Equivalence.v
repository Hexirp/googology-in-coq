(** 等価関数性です。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Dependent_Sum.
Require Googology_In_Coq.Product.
Require Googology_In_Coq.Pointwise_Path.
Require Googology_In_Coq.Pointwise_Path_Pointwise_Path.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Dependent_Sum (Dependent_Sum).
Import Googology_In_Coq.Product (Product).
Import Googology_In_Coq.Pointwise_Path (Pointwise_Path).
Import
  Googology_In_Coq.Pointwise_Path_Pointwise_Path
    (Pointwise_Path_Pointwise_Path)
.

(** ライブラリを開きます。 *)

Definition
  Is_Half_Adjoint_Equivalence@{i | } (A : Type@{i}) (B : Type@{i})
    : (A -> B) -> Type@{i}
    :=
      fun f : A -> B =>
        Dependent_Sum
          (B -> A)
          (
            fun g : B -> A =>
              Dependent_Sum
                (
                  Product
                    (Pointwise_Path A A (Function.comp A B A g f) (Function.id A))
                    (Pointwise_Path B B (Function.comp B A B f g) (Function.id B))
                )
                (
                  fun
                    p
                      :
                        Product
                          (Pointwise_Path A A (Function.comp A B A g f) (Function.id A))
                          (Pointwise_Path B B (Function.comp B A B f g) (Function.id B))
                  =>
                    Pointwise_Path_Pointwise_Path
                      (Function.comp A A B f (Function.comp A B A g f))
                      f
                      (Pointwise_Path.wisker_L A A B f (Function.comp A B A g f) (Function.id A) (Product.first (Pointwise_Path A A (Function.comp A B A g f) (Function.id A)) (Pointwise_Path B B (Function.comp B A B f g) (Function.id B)) p))
                      (Pointwise_Path.wisker_R A B B f (Function.comp B A B f g) (Function.id B) (Product.second (Pointwise_Path A A (Function.comp A B A g f) (Function.id A)) (Pointwise_Path B B (Function.comp B A B f g) (Function.id B)) p))
                )
          )
.
(* from: originally defined by Hexirp *)

(** 関数 [f] が等価関数であることです。 *)
