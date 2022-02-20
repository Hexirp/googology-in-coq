(** ウ型に関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.W_type_Alpha.
Require Googology_In_Coq.W_type_Beta.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.W_type_Alpha (W_type_Alpha).
Import Googology_In_Coq.W_type_Beta (W_type_Beta).

(** ライブラリを開きます。 *)

Inductive
  W_type@{i | } (A : Type@{i}) (B : A -> Type@{i}) : Type@{i}
    := sup : W_type_Alpha W_type_Beta W_type A B -> W_type A B
.
(* from: originally defined by Hexirp *)

(** ウ型です。 W-types です。 *)

(** [W_type] は [Alpha] と [W_type_Beta] という補助の型により定義されています。 *)

(** [Alpha] と [W_type_Beta] の組み立て方には複数の選択肢がありました。 *)

(** まず、 [Alpha] の定義の中で [W_type_Beta] を使うようにする方法がありました。しかし、 [W_type_Beta] が [Alpha] に依存することは許容できても [Alpha] が [W_type_Beta] に依存することは許容できませんでした。そのため、 [Alpha] の引数に [W_type_Beta] を渡すようにしました。 *)

(** 次に、 [Alpha] の引数として [W_type] を渡すのではなく [W_type A B] を渡す方法がありました。しかし、これでは [Alpha] の引数として [A] と [B] を渡した後に [W_type A B] を渡さなければならず、 [A] と [B] を 2 回書くことになってしまいます。これでは面倒くさいため、 [W_type] を渡すようにしました。 *)

(** 最終的に、 [W_type@{i}] は [forall (A : Type@{i}) (B : A -> Type@{i}), Type@{i}] という型の値で、 [Alpha@{i} W_type_Beta@{i}] は、 [forall (A : Type@{i}) (B : A -> Type@{i}), Type@{i}] を取って返す関数で、 [W_type@{i}] は [Alpha@{i} W_type_Beta@{i}] の不動点であるという風に定義されるようにしました。 *)

Definition
  matching@{i | }
      (A : Type@{i})
      (B : A -> Type@{i})
      (P : W_type A B -> Type@{i})
      (
        constructor_sup
          : forall x_v : W_type_Alpha W_type_Beta W_type A B, P (sup A B x_v)
      )
    : forall x : W_type A B, P x
    :=
      fun x : W_type A B =>
        match x as x_ return P x_ with sup _ _ x_v => constructor_sup x_v end
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  matching_nodep@{i | }
      (A : Type@{i})
      (B : A -> Type@{i})
      (P : Type@{i})
      (constructor_sup : W_type_Alpha W_type_Beta W_type A B -> P)
    : W_type A B -> P
    := matching A B (fun x_ : W_type A B => P) constructor_sup
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  induction@{i | }
      (A : Type@{i})
      (B : A -> Type@{i})
      (P : W_type A B -> Type@{i})
      (
        constructor_sup
          :
            forall
              x_v : W_type_Alpha W_type_Beta W_type A B
            ,
              (
                forall x_v_2_x : B (W_type_Alpha.first W_type_Beta W_type A B x_v),
                  P
                    (
                      W_type_Beta.apply
                        W_type
                        A
                        B
                        (W_type_Alpha.first W_type_Beta W_type A B x_v)
                        (W_type_Alpha.second W_type_Beta W_type A B x_v)
                        x_v_2_x
                    )
              )
            ->
              P (sup A B x_v)
      )
    : forall x : W_type A B, P x
    :=
      fix induction (x : W_type A B) {struct x} : P x :=
        matching
          A
          B
          P
          (
            fun
              x_v : W_type_Alpha W_type_Beta W_type A B
            =>
              constructor_sup
                x_v
                (
                  fun x_v_2_x : B (W_type_Alpha.first W_type_Beta W_type A B x_v) =>
                    induction
                      (
                        W_type_Beta.apply
                          W_type
                          A
                          B
                          (W_type_Alpha.first W_type_Beta W_type A B x_v)
                          (W_type_Alpha.second W_type_Beta W_type A B x_v)
                          x_v_2_x
                      )
                )
          )
          x
.
(* from: originally defined by Hexirp *)

(** 帰納法の原理です。 *)

Definition
  recursion@{i | }
      (A : Type@{i})
      (B : A -> Type@{i})
      (P : Type@{i})
      (
        constructor_sup
          :
            forall
              x_v : W_type_Alpha W_type_Beta W_type A B
            ,
              (B (W_type_Alpha.first W_type_Beta W_type A B x_v) -> P)
            ->
              P
      )
    : W_type A B -> P
    := induction A B (fun x_ => P) constructor_sup
.
(* from: originally defined by Hexirp *)

(** 再帰です。 *)

Definition
  map@{i | }
      (A : Type@{i})
      (B : A -> Type@{i})
      (C : Type@{i})
      (D : C -> Type@{i})
      (f : A -> C)
      (g : forall x : A, D (f x) -> B x)
    : W_type A B -> W_type C D
    :=
      recursion
        A
        B
        (W_type C D)
        (
          fun
            (x_v : W_type_Alpha W_type_Beta W_type A B)
            (y : B (W_type_Alpha.first W_type_Beta W_type A B x_v) -> W_type C D)
          =>
            sup
              C
              D
              (
                W_type_Alpha.pair
                  W_type_Beta
                  W_type
                  C
                  D
                  (f (W_type_Alpha.first W_type_Beta W_type A B x_v))
                  (
                    fun z : D (f (W_type_Alpha.first W_type_Beta W_type A B x_v)) =>
                      y (g (W_type_Alpha.first W_type_Beta W_type A B x_v) z)
                  )
              )
        )
.
(* from: originally defined by Hexirp *)

(** ウ型の写像です。 *)
