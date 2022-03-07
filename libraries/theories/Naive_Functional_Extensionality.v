(** 単純な関数外延性のモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Dependent_Function.
Require Googology_In_Coq.Function.
Require Googology_In_Coq.Product.
Require Googology_In_Coq.Universe.
Require Googology_In_Coq.Path.
Require Googology_In_Coq.Pointwise_Path.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Dependent_Function (Dependent_Function).
Import Googology_In_Coq.Function (Function).
Import Googology_In_Coq.Product (Product).
Import Googology_In_Coq.Path (Path).
Import Googology_In_Coq.Pointwise_Path (Pointwise_Path).

(** ライブラリを開きます。 *)

Inductive
  Naive_Functional_Extensionality@{i | }
      (A : Type@{i})
      (B : Type@{i})
    : Type@{i}
    :=
      wrap
        :
            Dependent_Function@{i}
              (Product@{i} (Function@{i} A B) (Function@{i} A B))
              (
                fun t : Product@{i} (Function@{i} A B) (Function@{i} A B) =>
                  Function@{i}
                    (
                      Pointwise_Path@{i}
                        A
                        B
                        (Product.first (Function@{i} A B) (Function@{i} A B) t)
                        (Product.second (Function@{i} A B) (Function@{i} A B) t)
                    )
                    (
                      Path@{i}
                        (Function@{i} A B)
                        (Product.first (Function@{i} A B) (Function@{i} A B) t)
                        (Product.second (Function@{i} A B) (Function@{i} A B) t)
                    )
              )
          ->
            Naive_Functional_Extensionality A B
.
(* from: originally defined by Hexirp *)

(** 単純な関数外延性です。 *)
