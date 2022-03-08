(** 等価関数性です。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Function.
Require Googology_In_Coq.Dependent_Sum.
Require Googology_In_Coq.Is_Half_Adjoint.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Function (Function).
Import Googology_In_Coq.Dependent_Sum (Dependent_Sum).
Import Googology_In_Coq.Is_Half_Adjoint (Is_Half_Adjoint).

(** ライブラリを開きます。 *)

Inductive
  Is_Half_Adjoint_Equivalence@{i | }
      (A : Type@{i})
      (B : Type@{i})
      (f : Function@{i} A B)
    : Type@{i}
    :=
      wrap
        :
            Dependent_Sum@{i}
              (Function@{i} B A)
              (fun g : Function:{i} B A => Is_Half_Adjoint A B f g)
          ->
            Is_Half_Adjoint_Equivalence A B f
.
(* from: originally defined by Hexirp *)

(** 関数 [f] が等価関数であることです。 *)
