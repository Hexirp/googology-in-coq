(** ウ型に関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Dependent_Sum.
Require Googology_In_Coq.W_type.Beta.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.W_type.Beta (Beta).

(** ライブラリを開きます。 *)

Module Alpha.

(** ウ型のアルファに関するモジュールです。 *)

Import Googology_In_Coq.Dependent_Sum (Dependent_Sum).

(** ライブラリを開きます。 *)

Definition
  Alpha@{i | }
      (
        beta
          :
            forall
              t : forall A : Type@{i}, (A -> Type@{i}) -> Type@{i}
            ,
            forall
              (A : Type@{i})
              (B : A -> Type@{i})
            ,
              A -> Type@{i}
      )
      (t : forall (A : Type@{i}) (B : A -> Type@{i}), Type@{i})
      (A : Type@{i})
      (B : A -> Type@{i})
    : Type@{i}
    := Dependent_Sum A (beta t A B)
.
(* from: originally defined by Hexirp *)

(** ウ型のアルファです。 *)

Definition
  pair@{i | }
      (
        beta
          :
            forall
              t : forall A : Type@{i}, (A -> Type@{i}) -> Type@{i}
            ,
            forall
              (A : Type@{i})
              (B : A -> Type@{i})
            ,
              A -> Type@{i}
      )
      (t : forall (A : Type@{i}) (B : A -> Type@{i}), Type@{i})
      (A : Type@{i})
      (B : A -> Type@{i})
      (a : A)
      (b : beta t A B a)
    : Alpha beta t A B
    := Dependent_Sum.pair A (beta t A B) a b
.
(* from: originally defined by Hexirp *)

(** ウ型のアルファの構築子です。 *)

Definition
  matching@{i | }
      (
        beta
          :
            forall
              t : forall A : Type@{i}, (A -> Type@{i}) -> Type@{i}
            ,
            forall
              (A : Type@{i})
              (B : A -> Type@{i})
            ,
              A -> Type@{i}
      )
      (t : forall (A : Type@{i}) (B : A -> Type@{i}), Type@{i})
      (A : Type@{i})
      (B : A -> Type@{i})
      (P : Alpha beta t A B -> Type@{i})
      (
        constructor_pair
          : forall (a : A) (b : beta t A B a), P (pair beta t A B a b)
      )
    : forall x : Alpha beta t A B, P x
    := Dependent_Sum.matching A (beta t A B) P constructor_pair
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  matching_nodep@{i | }
      (
        beta
          :
            forall
              t : forall A : Type@{i}, (A -> Type@{i}) -> Type@{i}
            ,
            forall
              (A : Type@{i})
              (B : A -> Type@{i})
            ,
              A -> Type@{i}
      )
      (t : forall (A : Type@{i}) (B : A -> Type@{i}), Type@{i})
      (A : Type@{i})
      (B : A -> Type@{i})
      (P : Type@{i})
      (constructor_pair : forall a : A, beta t A B a -> P)
    : Alpha beta t A B -> P
    := matching beta t A B (fun x_ : Alpha beta t A B => P) constructor_pair
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  first@{i | }
      (
        beta
          :
            forall
              t : forall A : Type@{i}, (A -> Type@{i}) -> Type@{i}
            ,
            forall
              (A : Type@{i})
              (B : A -> Type@{i})
            ,
              A -> Type@{i}
      )
      (t : forall (A : Type@{i}) (B : A -> Type@{i}), Type@{i})
      (A : Type@{i})
      (B : A -> Type@{i})
    : Alpha beta t A B -> A
    := matching_nodep beta t A B A (fun (a : A) (b : beta t A B a) => a)
.
(* from: originally defined by Hexirp *)

(** ウ型のアルファの第一射影関数です。 *)

Definition
  second@{i | }
      (
        beta
          :
            forall
              t : forall A : Type@{i}, (A -> Type@{i}) -> Type@{i}
            ,
            forall
              (A : Type@{i})
              (B : A -> Type@{i})
            ,
              A -> Type@{i}
      )
      (t : forall (A : Type@{i}) (B : A -> Type@{i}), Type@{i})
      (A : Type@{i})
      (B : A -> Type@{i})
    : forall x : Alpha beta t A B, beta t A B (first beta t A B x)
    :=
      matching
        beta
        t
        A
        B
        (fun x_ : Alpha beta t A B => beta t A B (first beta t A B x_))
        (fun (a : A) (b : beta t A B a) => b)
.
(* from: originally defined by Hexirp *)

(** ウ型のアルファの第二射影関数です。 *)

End Alpha.

Import Alpha (Alpha).

Inductive
  W_type@{i | } (A : Type@{i}) (B : A -> Type@{i}) : Type@{i}
    := sup : Alpha Beta W_type A B -> W_type A B
.
(* from: originally defined by Hexirp *)

(** ウ型です。 W-types です。 *)

(** [W_type] は [Alpha] と [Beta] という補助の型により定義されています。 *)

(** [Alpha] と [Beta] の組み立て方には複数の選択肢がありました。 *)

(** まず、 [Alpha] の定義の中で [Beta] を使うようにする方法がありました。しかし、 [Beta] が [Alpha] に依存することは許容できても [Alpha] が [Beta] に依存することは許容できませんでした。そのため、 [Alpha] の引数に [Beta] を渡すようにしました。 *)

(** 次に、 [Alpha] の引数として [W_type] を渡すのではなく [W_type A B] を渡す方法がありました。しかし、これでは [Alpha] の引数として [A] と [B] を渡した後に [W_type A B] を渡さなければならず、 [A] と [B] を 2 回書くことになってしまいます。これでは面倒くさいため、 [W_type] を渡すようにしました。 *)

(** 最終的に、 [W_type@{i}] は [forall (A : Type@{i}) (B : A -> Type@{i}), Type@{i}] という型の値で、 [Alpha@{i} Beta@{i}] は、 [forall (A : Type@{i}) (B : A -> Type@{i}), Type@{i}] を取って返す関数で、 [W_type@{i}] は [Alpha@{i} Beta@{i}] の不動点であるという風に定義されるようにしました。 *)

Definition
  matching@{i | }
      (A : Type@{i})
      (B : A -> Type@{i})
      (P : W_type A B -> Type@{i})
      (
        constructor_sup
          : forall x_v : Alpha Beta W_type A B, P (sup A B x_v)
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
      (constructor_sup : Alpha Beta W_type A B -> P)
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
              x_v : Alpha Beta W_type A B
            ,
              (
                forall x_v_2_x : B (Alpha.first Beta W_type A B x_v),
                  P
                    (
                      Beta.apply
                        W_type
                        A
                        B
                        (Alpha.first Beta W_type A B x_v)
                        (Alpha.second Beta W_type A B x_v)
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
              x_v : Alpha Beta W_type A B
            =>
              constructor_sup
                x_v
                (
                  fun x_v_2_x : B (Alpha.first Beta W_type A B x_v) =>
                    induction
                      (
                        Beta.apply
                          W_type
                          A
                          B
                          (Alpha.first Beta W_type A B x_v)
                          (Alpha.second Beta W_type A B x_v)
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
              x_v : Alpha Beta W_type A B
            ,
              (B (Alpha.first Beta W_type A B x_v) -> P)
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
            (x_v : Alpha Beta W_type A B)
            (y : B (Alpha.first Beta W_type A B x_v) -> W_type C D)
          =>
            sup
              C
              D
              (
                Alpha.pair
                  Beta
                  W_type
                  C
                  D
                  (f (Alpha.first Beta W_type A B x_v))
                  (
                    fun z : D (f (Alpha.first Beta W_type A B x_v)) =>
                      y (g (Alpha.first Beta W_type A B x_v) z)
                  )
              )
        )
.
(* from: originally defined by Hexirp *)

(** ウ型の写像です。 *)
