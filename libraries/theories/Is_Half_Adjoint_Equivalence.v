(** 等価関数性です。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Dependent_Sum.
Require Googology_In_Coq.Product.
Require Googology_In_Coq.Pointwise_Path.
Require Googology_In_Coq.Pointwise_Path_Pointwise_Path.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.Base.
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
                    (Pointwise_Path A A (Function.comp g f) Function.id)
                    (Pointwise_Path B B (Function.comp f g) Function.id)
                )
                (
                  Pointwise_Path_Pointwise_Path
                    (Function.comp f (Function.comp g f))
                    (Function.comp f (Function.comp g f))
                    (Pointwise_Path.wisker_L f (Product.first p))
                    (Pointwise_Path.wisker_R f (Product.second p))
                )
          )
.
(* from: originally defined by Hexirp *)

(** 関数 [f] が等価関数であることです。 *)
