(** 型の型です。 *)

Require Googology_In_Coq.Base.Base.
Require Googology_In_Coq.Base.Function.
Require Googology_In_Coq.Base.Product.
Require Googology_In_Coq.Base.Dependent_Sum.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を開きます。 *)

Definition T_ (R : forall X : Type, X -> X -> Type)
  : Type -> Type -> Type
  :=
    fun (A : Type) (B : Type) =>
      Dependent_Sum.T
        (A -> B)
        (
          fun f =>
            Product.T
              (
                Dependent_Sum.T
                  (B -> A)
                  (
                    fun g =>
                      Function.T_
                        B
                        (R B)
                        B
                        (R B)
                        (Function.comp f g)
                        Function.id
                  )
              )
              (
                Dependent_Sum.T
                  (B -> A)
                  (
                    fun h =>
                      Function.T_
                        A
                        (R A)
                        A
                        (R A)
                        (Function.comp h f)
                        Function.id
                  )
              )
        )
.
(* from: originally defined by Hexirp *)

(** 1-主型です。 *)
