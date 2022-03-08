(** 半随伴性です。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Function.
Require Googology_In_Coq.Dependent_Sum.
Require Googology_In_Coq.Product.
Require Googology_In_Coq.Pointwise_Path.
Require Googology_In_Coq.Pointwise_Path_Pointwise_Path.
Require Googology_In_Coq.Section.
Require Googology_In_Coq.Retraction.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Function (Function).
Import Googology_In_Coq.Dependent_Sum (Dependent_Sum).
Import Googology_In_Coq.Product (Product).
Import Googology_In_Coq.Pointwise_Path (Pointwise_Path).
Import Googology_In_Coq.Pointwise_Path_Pointwise_Path (Pointwise_Path_Pointwise_Path).
Import Googology_In_Coq.Section (Section).
Import Googology_In_Coq.Retraction (Retraction).

(** ライブラリを開きます。 *)

Inductive
  Is_Half_Adjoint@{i | }
      (A : Type@{i})
      (B : Type@{i})
      (f : Function@{i} A B)
      (g : Function@{i} B A)
    : Type@{i}
    :=
      wrap
        :
            Dependent_Sum
              (
                Product
                  (Retraction@{i} A B f g)
                  (Section@{i} A B f g)
              )
              (
                fun
                  p
                    :
                      Product
                        (Retraction@{i} A B f g)
                        (Section@{i} A B f g)
                =>
                  Pointwise_Path_Pointwise_Path
                    A
                    B
                    (Function.comp A A B f (Function.comp A B A g f))
                    f
                    (
                      Pointwise_Path.wisker_L
                        A
                        A
                        B
                        f
                        (Function.comp A B A g f)
                        (Function.id A)
                        (
                          Product.first
                            (Retraction@{i} A B f g)
                            (Section@{i} A B f g)
                            p
                        )
                    )
                    (
                      Pointwise_Path.wisker_R
                        A
                        B
                        B
                        (Function.comp B A B f g)
                        (Function.id B)
                        f
                        (
                          Product.second
                            (Retraction@{i} A B f g)
                            (Section@{i} A B f g)
                            p
                        )
                    )
              )
          ->
            Is_Half_Adjoint A B f g
.
(* from: originally defined by Hexirp *)

(** 関数 [f] と関数 [g] が半随伴であることです。 *)
