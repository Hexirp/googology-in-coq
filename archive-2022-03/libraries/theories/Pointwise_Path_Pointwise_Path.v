(** 点ごとの道の点ごとの道のモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Dependent_Function.
Require Googology_In_Coq.Function.
Require Googology_In_Coq.Path.
Require Googology_In_Coq.Pointwise_Path.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Dependent_Function (Dependent_Function).
Import Googology_In_Coq.Function (Function).
Import Googology_In_Coq.Path (Path).
Import Googology_In_Coq.Pointwise_Path (Pointwise_Path).

(** ライブラリを開きます。 *)

Inductive
  Pointwise_Path_Pointwise_Path@{i | }
      (A : Type@{i})
      (B : Type@{i})
      (f : Function@{i} A B)
      (g : Function@{i} A B)
      (p : Pointwise_Path@{i} A B f g)
      (q : Pointwise_Path@{i} A B f g)
    : Type@{i}
    :=
      wrap
        :
            Dependent_Function@{i}
              A
              (
                fun x : A =>
                  Path@{i}
                    (
                      Path@{i}
                        B
                        (Function.apply A B f x)
                        (Function.apply A B g x)
                    )
                    (Pointwise_Path.apply A B f g p x)
                    (Pointwise_Path.apply A B f g q x)
              )
          ->
            Pointwise_Path_Pointwise_Path A B f g p q
.
(* from: originally defined by Hexirp *)

(** 点ごとの道の点ごとの道です。 *)
