(** 等価構造です。 *)

Require Googology_In_Coq.Base.Base.
Require Googology_In_Coq.Base.Product.
Require Googology_In_Coq.Base.Dependent_Sum.
Require Googology_In_Coq.Base.Pointwise_Path.
Require Googology_In_Coq.Base.Pointwise_Path_Reasoning.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を開きます。 *)

Definition Has_Section (A : Type) (B : Type) (r : A -> B) : Type
  :=
    Dependent_Sum.T
      (B -> A)
      (fun s => Pointwise_Path.T B B (Function.comp r s) Function.id)
.
(* from: originally defined by Hexirp *)

(** 関数 [r] が切片を持つことです。あるいは、関数 [r] が引き込みであることです。 *)

Definition Is_Section (A : Type) (B : Type) (s : A -> B) : Type
  :=
    Dependent_Sum.T
      (B -> A)
      (fun r => Pointwise_Path.T A A (Function.comp r s) Function.id)
.
(* from: originally defined by Hexirp *)

(** 関数 [s] が切片であることです。あるいは、関数 [s] が引き込みを持つことです。 *)

Definition Is_Equivalence (A : Type) (B : Type) (f : A -> B) : Type
  := Product.T (Has_Section A B f) (Is_Section A B f)
.
(* from: originally defined by Hexirp *)

(** 関数 [f] が等価関数であることです。 *)

Definition Equivalence (A : Type) (B : Type) : Type
  := Dependent_Sum.T (A -> B) (fun f => Is_Equivalence A B f)
.
(* from: originally defined by Hexirp *)

(** 型 [A] と型 [B] の間の等価構造です。 *)

Definition id_is_equivalence (A : Type)
  : Is_Equivalence A A Function.id
.
Proof.
  unfold Is_Equivalence.
  unfold Has_Section.
  unfold Is_Section.
  refine (Product.pair _ _).
  -
    refine (Dependent_Sum.pair Function.id _).
    unfold Pointwise_Path.T.
    move=> x.
    exact Path.id.
  -
    refine (Dependent_Sum.pair Function.id _).
    unfold Pointwise_Path.T.
    move=> x.
    exact Path.id.
Defined.
(* from: originally defined by Hexirp *)

(** 関数 [Function.id] が等価関数であることです。 *)

Definition id {A : Type} : Equivalence A A
  := Dependent_Sum.pair Function.id (id_is_equivalence A).
(* from: originally defined by Hexirp *)

(** 等価構造が反射性を満たすことです。 *)

Definition comp_is_equivalence
    (A : Type)
    (B : Type)
    (C : Type)
    (f_0 : B -> C)
    (f_1 : A -> B)
  :
      Is_Equivalence B C f_0
    ->
      Is_Equivalence A B f_1
    ->
      Is_Equivalence A C (Function.comp f_0 f_1)
.
Proof.
  unfold Is_Equivalence.
  unfold Has_Section.
  unfold Is_Section.
  move=> H_0 H_1.
  refine (match H_0 with Product.pair H_0_a H_0_b => _ end).
  refine (match H_0_a with Dependent_Sum.pair g_0 H_0_a_b => _ end).
  refine (match H_0_b with Dependent_Sum.pair h_0 H_0_b_b => _ end).
  refine (match H_1 with Product.pair H_1_a H_1_b => _ end).
  refine (match H_1_a with Dependent_Sum.pair g_1 H_1_a_b => _ end).
  refine (match H_1_b with Dependent_Sum.pair h_1 H_1_b_b => _ end).
  refine (Product.pair _ _).
  -
    refine (Dependent_Sum.pair (Function.comp g_1 g_0) _).
    refine
      (
        Pointwise_Path_Reasoning.walk
          (Function.comp (Function.comp f_0 f_1) (Function.comp g_1 g_0))
          (Function.comp f_0 g_0)
          ?[d_0]
          _
      )
    .
    [d_0]: {
      change
        (
          Pointwise_Path.T
            C
            C
            (Function.comp f_0 (Function.comp (Function.comp f_1 g_1) g_0))
            (Function.comp f_0 (Function.comp  Function.id            g_0))
        )
      .
      refine (Pointwise_Path.wiskerLR f_0 g_0 _).
      exact H_1_a_b.
    }
    refine
      (
        Pointwise_Path_Reasoning.walk
          (Function.comp f_0 g_0)
          Function.id
          ?[d_1]
          _
      )
    .
    [d_1]: {
      exact H_0_a_b.
    }
    exact
      (
        Pointwise_Path_Reasoning.arrive
          Function.id
      )
    .
  -
    refine (Dependent_Sum.pair (Function.comp h_1 h_0) _).
    refine
      (
        Pointwise_Path_Reasoning.walk
          (Function.comp (Function.comp h_1 h_0) (Function.comp f_0 f_1))
          (Function.comp h_1 f_1)
          ?[d_0]
          _
      )
    .
    [d_0]: {
      change
        (
          Pointwise_Path.T
            A
            A
            (Function.comp h_1 (Function.comp (Function.comp h_0 f_0) f_1))
            (Function.comp h_1 (Function.comp  Function.id            f_1))
        )
      .
      refine (Pointwise_Path.wiskerLR h_1 f_1 _).
      exact H_0_b_b.
    }
    refine
      (
        Pointwise_Path_Reasoning.walk
          (Function.comp h_1 f_1)
          Function.id
          ?[d_1]
          _
      )
    .
    [d_1]: {
      exact H_1_b_b.
    }
    exact
      (
        Pointwise_Path_Reasoning.arrive
          Function.id
      )
    .
Defined.
(* from: originally defined by Hexirp *)

(** 等価関数 [f] と等価関数 [g] から等価関数 [Function.comp f g] が得られることです。 *)

Definition conc {A : Type} {B : Type} {C : Type}
  : Equivalence A B -> Equivalence B C -> Equivalence A C
.
Proof.
  unfold Equivalence.
  move=> H_0 H_1.
  refine (match H_0 with Dependent_Sum.pair f_0 H_0_b => _ end).
  refine (match H_1 with Dependent_Sum.pair f_1 H_1_b => _ end).
  refine (Dependent_Sum.pair (Function.comp f_1 f_0) _).
  exact (comp_is_equivalence A B C f_1 f_0 H_1_b H_0_b).
Defined.
(* from: originally defined by Hexirp *)

(** 等価構造が推移性を満たすことです。 *)

Definition Has_Quasi_Inverse (A : Type) (B : Type) (f : A -> B)
  :=
    Dependent_Sum.T
      (B -> A)
      (
        fun g =>
          Product.T
            (Pointwise_Path.T B B (Function.comp f g) Function.id)
            (Pointwise_Path.T A A (Function.comp g f) Function.id)
      )
.
(* from: originally defined by Hexirp *)

(** 関数 [f] が擬逆関数を持つことです。 *)

Definition Equivs_Is_Quinvs_First {A : Type} {B : Type} {f : A -> B}
  : Is_Equivalence A B f -> Has_Quasi_Inverse A B f
.
Proof.
  unfold Is_Equivalence.
  unfold Has_Section.
  unfold Is_Section.
  unfold Has_Quasi_Inverse.
  move=> H.
  refine (match H with Product.pair H_a H_b => _ end).
  refine (match H_a with Dependent_Sum.pair s H_a_b => _ end).
  refine (match H_b with Dependent_Sum.pair r H_b_b => _ end).
  refine (Dependent_Sum.pair s _).
  refine (Product.pair _ _).
  -
    exact H_a_b.
  -
    refine
      (
        Pointwise_Path_Reasoning.walk
          (Function.comp s f)
          (Function.comp r (Function.comp f (Function.comp s f)))
          ?[d_0]
          _
      )
    .
    [d_0]: {
      change
        (
          Pointwise_Path.T
            A
            A
            (Function.comp  Function.id        (Function.comp s f))
            (Function.comp (Function.comp r f) (Function.comp s f))
        )
      .
      refine (Pointwise_Path.wiskerR (Function.comp s f) _).
      exact (Pointwise_Path.inv H_b_b).
    }
    refine
      (
        Pointwise_Path_Reasoning.walk
          (Function.comp r (Function.comp f (Function.comp s f)))
          (Function.comp r f)
          ?[d_1]
          _
      )
    .
    [d_1]: {
      change
        (
          Pointwise_Path.T
            A
            A
            (Function.comp r (Function.comp (Function.comp f s) f))
            (Function.comp r (Function.comp  Function.id        f))
        )
      .
      refine (Pointwise_Path.wiskerLR r f _).
      exact H_a_b.
    }
    refine
      (
        Pointwise_Path_Reasoning.walk
          (Function.comp r f)
          Function.id
          ?[d_2]
          _
      )
    .
    [d_2]: {
      exact H_b_b.
    }
    exact
      (
        Pointwise_Path_Reasoning.arrive
          Function.id
      )
    .
Defined.
(* from: originally defined by Hexirp *)

(** 関数 [f] が等価関数であるならば擬逆関数を持つことです。 *)
