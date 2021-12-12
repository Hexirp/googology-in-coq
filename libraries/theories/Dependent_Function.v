(** 依存関数型のモジュールです。 *)

Require Googology_In_Coq.Base.

(** [Googology_In_Coq.Base] を要求します。 *)

Import Googology_In_Coq.Base.

(** [Googology_In_Coq.Base] を開きます。 *)

Axiom Dependent_Function@{i j | }
  :
    forall A : Type@{i}, (A -> Type@{j}) -> Type@{j}
.
(* from: originally defined by Hexirp *)

(** 依存関数型です。 *)

Axiom abstract@{i j | }
  :
    forall
      (A : Type@{i})
      (B : A -> Type@{j})
    ,
      (forall x : A, B x) -> Dependent_Function@{i j} A B
.

(** 抽象です。ラムダ抽象です。 *)

Axiom apply@{i j | }
  :
    forall                                                                            (A : Type@{i})
      (B : A -> Type@{j})
    ,
      Dependent_Function@{i j} A B -> forall x : A, B x
.

(** 適用です。 *)
