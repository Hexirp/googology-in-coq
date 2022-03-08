(** 引き込みの型です。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Function.
Require Googology_In_Coq.Pointwise_Path.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Function (Function).
Import Googology_In_Coq.Pointwise_Path (Pointwise_Path).

(** ライブラリを開きます。 *)

Inductive
  Retraction@{i | }
      (A : Type@{i})
      (B : Type@{i})
      (f : Function@{i} A B)
      (g : Function@{i} B A)
    : Type@{i}
    :=
      wrap
        :
            Pointwise_Path@{i} A A (Function.comp A B A g f) (Function.id A)
          ->
            Retraction A B f g
.
(* from: originally defined by Hexirp *)

(** 引き込みの型です。 *)

(** 名前の由来は [f] が引き込み (retraction) であることの証明を偶然にも此の型が与えていることです。 *)

Definition
  unwrap@{i | }
      (A : Type@{i})
      (B : Type@{i})
      (f : Function@{i} A B)
      (g : Function@{i} B A)
    :
        Retraction@{i} A B f g
      ->
        Pointwise_Path@{i} A A (Function.comp A B A g f) (Function.id A)
    :=
      fun x : Retraction@{i} A B f g =>
        match x with wrap _ _ _ _ x_v => x_v end
.
(* from: originally defined by Hexirp *)

(** 切断の型です。 *)
