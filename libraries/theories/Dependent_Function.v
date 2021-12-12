(** 依存関数型のモジュールです。 *)

Require Googology_In_Coq.Base.

(** [Googology_In_Coq.Base] を要求します。 *)

Import Googology_In_Coq.Base.

(** [Googology_In_Coq.Base] を開きます。 *)

Definition Dependent_Function@{i | }
    (A : Type@{i})
    (B : A -> Type@{i})
  : Type@{i}
  := forall x : A, B x
.
(* from: originally defined by Hexirp *)

(** 依存関数型です。 *)

Definition abstract@{i | }
    (A : Type@{i})
    (B : A -> Type@{j})
    (x : forall x : A, B x)
  : Dependent_Function@{i j} A B
  := x
.

(** 抽象です。ラムダ抽象です。 *)

Definition apply@{i j | }
    (A : Type@{i})
    (B : A -> Type@{j})
    (x : Dependent_Function@{i j} A B)
  : forall x : A, B x
  := x
.

(** 適用です。 *)
