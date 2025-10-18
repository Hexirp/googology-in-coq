(** 等価構造です。 *)

Require Googology_In_Coq.Base.Base.
Require Googology_In_Coq.Base.Product.
Require Googology_In_Coq.Base.Dependent_Sum.
Require Googology_In_Coq.Base.Pointwise_Path.
Require Googology_In_Coq.Base.Pointwise_Path_Reasoning.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.Base.

(** [Googology_In_Coq.Base.Base] を開きます。 *)

Definition Has_Section {A : Type} {B : Type} (r : A -> B) : Type
  :=
    Dependent_Sum.T
      (B -> A)
      (fun s => Pointwise_Path.T (Function.comp r s) Function.id)
.
(* from: originally defined by Hexirp *)

(** 関数 [r] が切片を持つことです。あるいは、関数 [r] が引き込みであることです。 *)

Definition Is_Section {A : Type} {B : Type} (s : A -> B) : Type
  :=
    Dependent_Sum.T
      (B -> A)
      (fun r => Pointwise_Path.T (Function.comp r s) Function.id)
.
(* from: originally defined by Hexirp *)

(** 関数 [s] が切片であることです。あるいは、関数 [s] が引き込みを持つことです。 *)

Definition Is_Equivalence {A : Type} {B : Type} (f : A -> B) : Type
  := Product.T (Has_Section f) (Is_Section f)
.
(* from: originally defined by Hexirp *)

(** 関数 [f] が等価関数であることです。 *)

Definition Equivalence (A : Type) (B : Type) : Type
  := Dependent_Sum.T (A -> B) (fun f => Is_Equivalence f)
.
(* from: originally defined by Hexirp *)

(** 型 [A] と型 [B] の間の等価構造です。 *)

Definition id_is_equivalence (A : Type)
  : Is_Equivalence (Function.id_visible A)
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
      Is_Equivalence f_0
    ->
      Is_Equivalence f_1
    ->
      Is_Equivalence (Function.comp f_0 f_1)
.
Proof.
  unfold Is_Equivalence.
  unfold Has_Section.
  unfold Is_Section.
  move=> H_0 H_1.
  refine (Product.pair _ _).
  -
    refine
      (
        Dependent_Sum.pair
          (
            Function.comp
              (Dependent_Sum.first (Product.first H_1))
              (Dependent_Sum.first (Product.first H_0))
          )
          _
      )
    .
    refine
      (
        Pointwise_Path_Reasoning.walk
          (
            Function.comp
              (
                Function.comp
                  f_0
                  f_1
              )
              (
                Function.comp
                  (Dependent_Sum.first (Product.first H_1))
                  (Dependent_Sum.first (Product.first H_0))
              )
          )
          (
            Function.comp
              f_0
              (Dependent_Sum.first (Product.first H_0))
          )
          ?[d_0]
          _
      )
    .
    [d_0]: {
      change
        (
          Pointwise_Path.T
            (
              Function.comp
                f_0
                (
                  Function.comp
                    (
                      Function.comp
                        f_1
                        (Dependent_Sum.first (Product.first H_1))
                    )
                    (Dependent_Sum.first (Product.first H_0))
                )
            )
            (
              Function.comp
                f_0
                (
                  Function.comp
                    Function.id
                    (Dependent_Sum.first (Product.first H_0))
                )
            )
        )
      .
      refine
        (
          Pointwise_Path.wisker_L_R
            f_0
            (Dependent_Sum.first (Product.first H_0))
            _
        )
      .
      exact (Dependent_Sum.second (Product.first H_1)).
    }
    refine
      (
        Pointwise_Path_Reasoning.walk
          (
            Function.comp
              f_0
              (Dependent_Sum.first (Product.first H_0))
          )
          Function.id
          ?[d_1]
          _
      )
    .
    [d_1]: {
      exact (Dependent_Sum.second (Product.first H_0)).
    }
    exact
      (
        Pointwise_Path_Reasoning.arrive
          Function.id
      )
    .
  -
    refine
      (
        Dependent_Sum.pair
          (
            Function.comp
              (Dependent_Sum.first (Product.second H_1))
              (Dependent_Sum.first (Product.second H_0))
          )
          _
      )
    .
    refine
      (
        Pointwise_Path_Reasoning.walk
          (
            Function.comp
              (
                Function.comp
                  (Dependent_Sum.first (Product.second H_1))
                  (Dependent_Sum.first (Product.second H_0))
              )
              (
                Function.comp
                  f_0
                  f_1
              )
          )
          (
            Function.comp
              (Dependent_Sum.first (Product.second H_1))
              f_1
          )
          ?[d_0]
          _
      )
    .
    [d_0]: {
      change
        (
          Pointwise_Path.T
            (
              Function.comp
                (Dependent_Sum.first (Product.second H_1))
                (
                  Function.comp
                    (
                      Function.comp
                        (Dependent_Sum.first (Product.second H_0))
                        f_0
                    )
                    f_1
                )
            )
            (
              Function.comp
                (Dependent_Sum.first (Product.second H_1))
                (
                  Function.comp
                    Function.id
                    f_1
                )
            )
        )
      .
      refine
        (
          Pointwise_Path.wisker_L_R
            (Dependent_Sum.first (Product.second H_1))
            f_1
            _
        )
      .
      exact (Dependent_Sum.second (Product.second H_0)).
    }
    refine
      (
        Pointwise_Path_Reasoning.walk
          (
            Function.comp
              (Dependent_Sum.first (Product.second H_1))
              f_1
          )
          Function.id
          ?[d_1]
          _
      )
    .
    [d_1]: {
      exact (Dependent_Sum.second (Product.second H_1)).
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
  refine
    (
      Dependent_Sum.pair
        (Function.comp (Dependent_Sum.first H_1) (Dependent_Sum.first H_0))
        _
    )
  .
  exact
    (
      comp_is_equivalence
        A
        B
        C
        (Dependent_Sum.first H_1)
        (Dependent_Sum.first H_0)
        (Dependent_Sum.second H_1)
        (Dependent_Sum.second H_0)
    )
  .
Defined.
(* from: originally defined by Hexirp *)

(** 等価構造が推移性を満たすことです。 *)

Definition Has_Quasi_Inverse {A : Type} {B : Type} (f : A -> B)
  :=
    Dependent_Sum.T
      (B -> A)
      (
        fun g =>
          Product.T
            (Pointwise_Path.T (Function.comp f g) Function.id)
            (Pointwise_Path.T (Function.comp g f) Function.id)
      )
.
(* from: originally defined by Hexirp *)

(** 関数 [f] が擬逆関数を持つことです。 *)

Definition Equivs_Is_Quinvs_First {A : Type} {B : Type} {f : A -> B}
  : Is_Equivalence f -> Has_Quasi_Inverse f
.
Proof.
  unfold Is_Equivalence.
  unfold Has_Section.
  unfold Is_Section.
  unfold Has_Quasi_Inverse.
  move=> H.
  refine
    (
      Dependent_Sum.pair
        (Dependent_Sum.first (Product.first H))
        _
    )
  .
  refine (Product.pair _ _).
  -
    exact (Dependent_Sum.second (Product.first H)).
  -
    refine
      (
        Pointwise_Path_Reasoning.walk
          (
            Function.comp
              (Dependent_Sum.first (Product.first H))
              f
          )
          (
            Function.comp
              (Dependent_Sum.first (Product.second H))
              (
                Function.comp
                  f
                  (
                    Function.comp
                      (Dependent_Sum.first (Product.first H))
                      f
                  )
              )
          )
          ?[d_0]
          _
      )
    .
    [d_0]: {
      change
        (
          Pointwise_Path.T
            (
              Function.comp
                Function.id
                (
                  Function.comp
                    (Dependent_Sum.first (Product.first H))
                    f
                )
            )
            (
              Function.comp
                (
                  Function.comp
                    (Dependent_Sum.first (Product.second H))
                    f
                )
                (
                  Function.comp
                    (Dependent_Sum.first (Product.first H))
                    f
                )
            )
        )
      .
      refine
        (
          Pointwise_Path.wisker_R
          (
            Function.comp
              (Dependent_Sum.first (Product.first H))
              f
          )
          _
        )
      .
      exact
        (
          Pointwise_Path.inv (Dependent_Sum.second (Product.second H))
        )
      .
    }
    refine
      (
        Pointwise_Path_Reasoning.walk
          (
            Function.comp
              (Dependent_Sum.first (Product.second H))
              (
                Function.comp
                  f
                  (
                    Function.comp
                      (Dependent_Sum.first (Product.first H))
                      f
                  )
              )
          )
          (
            Function.comp
              (Dependent_Sum.first (Product.second H))
              f
          )
          ?[d_1]
          _
      )
    .
    [d_1]: {
      change
        (
          Pointwise_Path.T
            (
              Function.comp
                (Dependent_Sum.first (Product.second H))
                (
                  Function.comp
                    (
                      Function.comp
                        f
                        (Dependent_Sum.first (Product.first H))
                    )
                    f
                )
            )
            (
              Function.comp
                (Dependent_Sum.first (Product.second H))
                (
                  Function.comp
                    Function.id
                    f
                )
            )
        )
      .
      refine
        (
          Pointwise_Path.wisker_L_R
            (Dependent_Sum.first (Product.second H))
            f
            _
        )
      .
      exact (Dependent_Sum.second (Product.first H)).
    }
    refine
      (
        Pointwise_Path_Reasoning.walk
          (
            Function.comp
              (Dependent_Sum.first (Product.second H))
              f
          )
          Function.id
          ?[d_2]
          _
      )
    .
    [d_2]: {
      exact (Dependent_Sum.second (Product.second H)).
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
