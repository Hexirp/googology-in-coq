(** 切断の型です。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Function.
Require Googology_In_Coq.Pointwise_Path.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Function (Function).
Import Googology_In_Coq.Pointwise_Path (Pointwise_Path).

(** ライブラリを開きます。 *)

Inductive
  Section@{i | }
      (A : Type@{i})
      (B : Type@{i})
      (f : Function@{i} A B)
      (g : Function@{i} B A)
    : Type@{i}
    :=
      wrap
        :
            Pointwise_Path@{i} B B (Function.comp B A B f g) (Function.id B)
          ->
            Section A B f g
.
(* from: originally defined by Hexirp *)

(** 切断の型です。 *)

(** 名前の由来は [f] が切断 (section) であることの証明を偶然にも此の型が与えていることです。 *)

Definition
  unwrap@{i | }
      (A : Type@{i})
      (B : Type@{i})
      (f : Function@{i} A B)
      (g : Function@{i} B A)
    :
        Section@{i} A B f g
      ->
        Pointwise_Path@{i} B B (Function.comp B A B f g) (Function.id B)
    := fun x : Section@{i} A B f g => match x with wrap _ _ _ _ x_v => x_v end
.
(* from: originally defined by Hexirp *)

(** 切断の型です。 *)
