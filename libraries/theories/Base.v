(** [Googology_In_Coq.Base] は基本的な定義を提供します。 *)

Require Googology_In_Coq.Base.Base.
Require Googology_In_Coq.Base.Function.
Require Googology_In_Coq.Base.Dependent_Function.
Require Googology_In_Coq.Base.Unit.
Require Googology_In_Coq.Base.Void.
Require Googology_In_Coq.Base.Product.
Require Googology_In_Coq.Base.Sum.
Require Googology_In_Coq.Base.Dependent_Product.
Require Googology_In_Coq.Base.Dependent_Sum.
Require Googology_In_Coq.Base.Path.
Require Googology_In_Coq.Base.TYPE.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を開きます。 *)















(** 道での等式推論です。 *)

Module Path_Reasoning.

(** 1 ステップ分先に進みます。 *)

(* from: originally defined by Hexirp *)
Definition walk
    {A : Type}
    (old_start_term : A)
    (new_start_term : A)
    {goal_term : A}
    (step : Path.T old_start_term new_start_term)
    (rest : Path.T new_start_term goal_term)
  : Path.T old_start_term goal_term
  := Path.conc step rest
.

(** 終了します。 *)

(* from: originally defined by Hexirp *)
Definition arrive
  {A : Type}
  (goal_term : A)
  : Path.T goal_term goal_term
  := Path.id
.

End Path_Reasoning.

(** 点ごとの道です。 *)

Module Pointwise_Path.

(** 主型です。 *)

(* from: originally defined by Hexirp *)
Definition T (A : Type) (B : Type)
  : (A -> B) -> (A -> B) -> Type
  :=
    fun (f : A -> B) (g : A -> B) =>
      forall x : A, Path.T (f x) (g x)
.

(** [Function.T_] への変換です。 *)

(* from: originally defined by Hexirp *)
Definition to_Function_1 (A : Type) (B : Type)
  :
    forall (f : A -> B) (g : A -> B),
      T A B f g -> Function.T_ A (@Path.T A) B (@Path.T B) f g
.
Proof.
  move=> f g.
  unfold T; unfold Function.T_.
  move=> h.
  move=> x y.
  move=> p.
  refine (let D := fun y : A => Path.T (f x) (g y) in _).
  change (D y).
  refine (Path.trpt p _).
  exact (h x).
Defined.

(** [Function.T_] からの変換です。 *)

(* from: originally defined by Hexirp *)
Definition from_Function_1 (A : Type) (B : Type)
  :
    forall (f : A -> B) (g : A -> B),
      Function.T_ A (@Path.T A) B (@Path.T B) f g -> T A B f g
.
Proof.
  move=> f g.
  unfold Function.T_; unfold T.
  move=> h.
  move=> x.
  exact (h x x Path.id).
Defined.

(** 点ごとの道の恒等道です。 *)

(* from: originally defined by Hexirp *)
Definition id {A : Type} {B : Type}{f : A -> B}
  : T A B f f
  := fun x : A => Path.id
.


(** 点ごとの道の合成です。 *)

(* from: originally defined by Hexirp *)
Definition conc
    {A : Type}
    {B : Type}
    {f : A -> B}
    {g : A -> B}
    {h : A -> B}
  : T A B f g -> T A B g h -> T A B f h
.
Proof.
  unfold T.
  move=> p q.
  move=> x.
  exact (Path.conc (p x) (q x)).
Defined.

(** 点ごとの道の逆です。 *)

(* from: originally defined by Hexirp *)
Definition inv
    {A : Type}
    {B : Type}
    {f : A -> B}
    {g : A -> B}
  : T A B f g -> T A B g f
.
Proof.
  unfold T.
  move=> p.
  move=> x.
  exact (Path.inv (p x)).
Defined.

(** 左からの髭つけです。 *)

(* from: originally defined by Hexirp *)
Definition wiskerL
    {A : Type}
    {B : Type}
    {C : Type}
    (f : B -> C)
    {g : A -> B}
    {h : A -> B}
  : T A B g h -> T A C (Function.comp f g) (Function.comp f h)
.
Proof.
  unfold T.
  move=> p.
  move=> x.
  exact (Path.ap f (p x)).
Defined.

(** 右からの髭つけです。 *)

(* from: originally defined by Hexirp *)
Definition wiskerR
    {A : Type}
    {B : Type}
    {C : Type}
    (f : A -> B)
    {g : B -> C}
    {h : B -> C}
  : T B C g h -> T A C (Function.comp g f) (Function.comp h f)
.
Proof.
  unfold T.
  move=> p.
  move=> x.
  exact (p (f x)).
Defined.

(** 左右からの髭つけです。 *)

(* from: originally defined by Hexirp *)
Definition wiskerLR
    {A : Type}
    {B : Type}
    {C : Type}
    {D : Type}
    (f_0 : C -> D)
    (f_1 : A -> B)
    {g : B -> C}
    {h : B -> C}
  :
      T B C g h
    ->
      T
        A
        D
        (Function.comp f_0 (Function.comp g f_1))
        (Function.comp f_0 (Function.comp h f_1))
  := fun p : T B C g h => wiskerL f_0 (wiskerR f_1 p)
.

End Pointwise_Path.

(** 点ごとの道での等式推論です。 *)

Module Pointwise_Path_Reasoning.

(** 1 ステップ分先に進みます。 *)

(* from: originally defined by Hexirp *)
Definition walk
    {A B : Type}
    (old_start_term : A -> B)
    (new_start_term : A -> B)
    {goal_term : A -> B}
    (step : Pointwise_Path.T A B old_start_term new_start_term)
    (rest : Pointwise_Path.T A B new_start_term goal_term)
  : Pointwise_Path.T A B old_start_term goal_term
  := Pointwise_Path.conc step rest
.

(** 終了します。 *)

(* from: originally defined by Hexirp *)
Definition arrive
  {A B : Type}
  (goal_term : A -> B)
  : Pointwise_Path.T A B goal_term goal_term
  := Pointwise_Path.id
.

End Pointwise_Path_Reasoning.

(** 等価構造です。 *)

Module Equivalence.

(** 関数 [r] が切片を持つことです。あるいは、関数 [r] が引き込みであることです。 *)

(* from: originally defined by Hexirp *)
Definition Has_Section (A : Type) (B : Type) (r : A -> B) : Type
  :=
    Dependent_Sum.T
      (B -> A)
      (fun s => Pointwise_Path.T B B (Function.comp r s) Function.id)
.

(** 関数 [s] が切片であることです。あるいは、関数 [s] が引き込みを持つことです。 *)

(* from: originally defined by Hexirp *)
Definition Is_Section (A : Type) (B : Type) (s : A -> B) : Type
  :=
    Dependent_Sum.T
      (B -> A)
      (fun r => Pointwise_Path.T A A (Function.comp r s) Function.id)
.

(** 関数 [f] が等価関数であることです。 *)

(* from: originally defined by Hexirp *)
Definition Is_Equivalence (A : Type) (B : Type) (f : A -> B) : Type
  := Product.T (Has_Section A B f) (Is_Section A B f)
.

(** 型 [A] と型 [B] の間の等価構造です。 *)

(* from: originally defined by Hexirp *)
Definition T (A : Type) (B : Type) : Type
  := Dependent_Sum.T (A -> B) (fun f => Is_Equivalence A B f)
.

(** [TYPE.T_] への変換です。 *)

(* from: originally defined by Hexirp *)
Definition to_TYPE_1
  : forall (A : Type) (B : Type), T A B -> TYPE.T_ (@Path.T) A B
.
Proof.
  move=> A B.
  unfold T.
  unfold Is_Equivalence.
  unfold Has_Section.
  unfold Is_Section.
  unfold TYPE.T_.
  refine (Dependent_Sum.map _).
  move=> f.
  refine (Product.map _ _).
  -
    refine (Dependent_Sum.map _).
    move=> g.
    exact (Pointwise_Path.to_Function_1 B B (Function.comp f g) Function.id).
  -
    refine (Dependent_Sum.map _).
    move=> h.
    exact (Pointwise_Path.to_Function_1 A A (Function.comp h f) Function.id).
Defined.

(** [TYPE.T_] からの変換です。 *)

(* from: originally defined by Hexirp *)
Definition from_TYPE_1
  : forall (A : Type) (B : Type), TYPE.T_ (@Path.T) A B -> T A B
.
Proof.
  move=> A B.
  unfold T.
  unfold Is_Equivalence.
  unfold Has_Section.
  unfold Is_Section.
  unfold TYPE.T_.
  refine (Dependent_Sum.map _).
  move=> f.
  refine (Product.map _ _).
  -
    refine (Dependent_Sum.map _).
    move=> g.
    exact (Pointwise_Path.from_Function_1 B B (Function.comp f g) Function.id).
  -
    refine (Dependent_Sum.map _).
    move=> h.
    exact (Pointwise_Path.from_Function_1 A A (Function.comp h f) Function.id).
Defined.

(** 関数 [Function.id] が等価関数であることです。 *)

(* from: originally defined by Hexirp *)
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

(** 等価構造が反射性を満たすことです。 *)

(* from: originally defined by Hexirp *)
Definition id {A : Type} : T A A
  := Dependent_Sum.pair Function.id (id_is_equivalence A).

(** 等価関数 [f] と等価関数 [g] から等価関数 [Function.comp f g] が得られることです。 *)

(* from: originally defined by Hexirp *)
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

(** 等価構造が推移性を満たすことです。 *)

(* from: originally defined by Hexirp *)
Definition conc {A : Type} {B : Type} {C : Type}
  : T A B -> T B C -> T A C
.
Proof.
  unfold T.
  move=> H_0 H_1.
  refine (match H_0 with Dependent_Sum.pair f_0 H_0_b => _ end).
  refine (match H_1 with Dependent_Sum.pair f_1 H_1_b => _ end).
  refine (Dependent_Sum.pair (Function.comp f_1 f_0) _).
  exact (comp_is_equivalence A B C f_1 f_0 H_1_b H_0_b).
Defined.

(** 関数 [f] が擬逆関数を持つことです。 *)

(* from: originally defined by Hexirp *)
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

(** 関数 [f] が等価関数であるならば擬逆関数を持つことです。 *)

(* from: originally defined by Hexirp *)
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

End Equivalence.

Module Natural_Number.

Module Peano.

Inductive T : Type := zero : T | successor : T -> T.

End Peano.

End Natural_Number.
