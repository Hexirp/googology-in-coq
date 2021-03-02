(* Run with -nois. *)
(** [GiC.Type.Nat] は自然数に関する基本的な定義を提供します。

    具体的には、 [plus] や [lt] などを定義します。
 *)

(** 必要なライブラリを要求します。 *)

Require GiC.Base.
Require GiC.Type.Base.

(** 必要なモジュールをインポートします。 *)

Import GiC.Base.
Import GiC.Type.Base.

(** 帰納原理 (induction principle) を生成しないように設定します。 *)

Unset Elimination Schemes.

(** 宇宙多相 (universe polymorphism) について設定します。 *)

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

(** タクティックが使用できるように設定します。 *)

Set Default Proof Mode "Classic".

(** ビュレットを使用しないときにエラーになるように設定します。 *)

Set Default Goal Selector "!".

(** ** 基本的な不平等の定理です。 *)

(** [Path zero (succ n) -> Void] です。 *)

(* from: originally defined by Hexirp *)
Definition fun_Path_zero_succ_n_Void@{i si | i < si}
  : forall n : Nat@{i}, Path@{i} zero@{i} (succ n) -> Void@{i}.
Proof.
  refine (fun n x => _).
  refine (pUV@{i si} _).
  refine (let d := ?[d] : Nat@{i} -> Type@{i} in _).
  [d]: {
    refine (fun x => _).
    refine (match x with zero => _ | succ xp => _ end).
    -
      exact Unit@{i}.
    -
      exact Void@{i}.
  }
  exact (ap d x).
Defined.

(** ** 基本的な述語です。 *)

(** [y] が [x] 以上であることです。 *)

(* from: originally defined by Hexirp *)
Inductive Le@{i | } (x y : Nat@{i}) : Type@{i} :=
  | zero_Le : Path@{i} x y -> Le x y
  | succ_Le
    : forall yp : Nat@{i}, Path@{i} y (succ yp) -> Le x yp -> Le x y.

(** [Le n n] です。 *)

(* from: originally defined by Hexirp *)
Definition le_n_n@{i | } : forall n : Nat@{i}, Le@{i} n n.
Proof.
  refine (fun n => _).
  refine (zero_Le n n _).
  exact idpath.
Defined.

(** [Le m (succ n)] です。 *)

(* from: originally defined by Hexirp *)
Definition le_m_succ_n@{i | } (m n : Nat@{i}) : Le m n -> Le m (succ n).
Proof.
  refine (fun x => _).
  refine (succ_Le m (succ n) n _ _).
  -
    exact idpath.
  -
    exact x.
Defined.

(** [Le zero n] です。 *)

(* from: originally defined by Hexirp *)
Definition le_zero_n@{i | } : forall n : Nat@{i}, Le@{i} zero n.
Proof.
  refine (fix t (n : Nat@{i}) {struct n} : Le@{i} zero n := _).
  refine (match n with zero => _ | succ np => _ end).
  -
    exact (le_n_n zero).
  -
    refine (le_m_succ_n zero np _).
    exact (t np).
Defined.

(** [Le (succ m) zero -> Void] です。 *)

(* from: originally defined by Hexirp *)
Definition fun_Le_succ_m_zero_Void@{i si | i < si}
  : forall m : Nat@{i}, Le@{i} (succ m) zero -> Void@{i}.
Proof.
  refine (fun m x => _).
  refine (match x with zero_Le _ _ h => _ | succ_Le _ _ np h xp => _ end).
  -
    refine (fun_Path_zero_succ_n_Void@{i si} m _).
    exact (inv h).
  -
    refine (fun_Path_zero_succ_n_Void@{i si} np _).
    exact h.
Defined.

(** [Le m n -> Le (succ m) (succ n)] です。 *)

(* from: originally defined by Hexirp *)
Definition fun_le_m_n_le_succ_m_succ_n@{i | }
  : forall m n : Nat@{i}, Le m n -> Le (succ m) (succ n).
Proof.
  refine
    (fix t (m n : Nat@{i}) (h : Le m n) {struct m} : Le (succ m) (succ n)
      := _).
  refine (match m with zero => _ | succ mp => _ end).
  -
    refine (match n with zero => _ | succ np => _ end).
    +
      admit.
    +
      admit.
  -
    admit.
Admitted.

(** [y] が [x] より大きいことです。 *)

(* from: originally defined by Hexirp *)
Definition Lt@{i | } (x y : Nat@{i}) : Type@{i} := Le@{i} (succ x) y.

(** [x] と [y] が等しいかどうかです。 *)

(* from: originally defined by Hexirp *)
Definition eq@{i | } : Nat@{i} -> Nat@{i} -> Bool@{i} :=
  fix t (x y : Nat@{i}) {struct x} : Bool@{i} :=
    match x
      with
        | zero =>
          match y
            with
              | zero => true
              | succ yp => false
          end
        | succ xp =>
          match y
            with
              | zero => false
              | succ yp => t xp yp
          end
    end.

(** [y] が [x] 以上であるかどうかです。 *)

(* from: originally defined by Hexirp *)
Definition le@{i | } : Nat@{i} -> Nat@{i} -> Bool@{i} :=
  fix t (x y : Nat@{i}) {struct x} : Bool@{i} :=
    match x
      with
        | zero => true
        | succ xp =>
          match y
            with
              | zero => false
              | succ yp => t xp yp
          end
    end.

(** [Path (le zero n) true] です。 *)

(* from: originally defined by Hexirp *)
Definition path_le_zero_n_true@{i | }
  : forall n : Nat@{i}, Path@{i} (le@{i} zero n) true.
Proof.
  refine (fun n => _).
  simpl.
  exact idpath.
Defined.

(** [Path (le (succ m) zero) false] です。 *)

(* from: originally defined by Hexirp *)
Definition path_le_succ_m_zero_false@{i | }
  : forall m : Nat@{i}, Path (le (succ m) zero) false.
Proof.
  refine (fun m => _).
  simpl.
  exact idpath.
Defined.

(** [y] が [x] より大きいかどうかです。 *)

(* from: originally defined by Hexirp *)
Definition lt@{i | } : Nat@{i} -> Nat@{i} -> Bool@{i} :=
  fix t (x y : Nat@{i}) {struct x} : Bool@{i} :=
    match x
      with
        | zero =>
          match y
            with
              | zero => false
              | succ yp => true
          end
        | succ xp =>
          match y
            with
              | zero => false
              | succ yp => t xp yp
          end
    end.

(** [le] が [Le] を反射していることです。 *)

(* from: originally defined by Hexirp *)
Definition reflect_Le_m_n_le_m_n@{i | }
  : forall m n : Nat@{i}, Reflect@{i} (Le@{i} m n) (le m n).
Proof.
  refine
    (fix t (m n : Nat@{i}) {struct m} : Reflect@{i} (Le@{i} m n) (le m n)
      := _).
  refine (match m with zero => _ | succ mp => _ end).
  -
    refine (pos_Reflect _ _).
    +
      exact (le_zero_n n).
    +
      exact (path_le_zero_n_true n).
  -
    refine (match n with zero => _ | succ np => _ end).
    +
      refine (neg_Reflect _ _).
      *
        exact (fun_Le_succ_m_zero_Void mp).
      *
        exact (path_le_succ_m_zero_false mp).
    +
      refine
        (match t mp np
          with pos_Reflect pH ph => _ | neg_Reflect nH nh => _
        end).
      *
        refine (pos_Reflect _ _).
        --
          refine (fun_le_m_n_le_succ_m_succ_n mp np _).
          exact pH.
        --
          admit.
      *
        refine (neg_Reflect _ _).
        --
          admit.
        --
          admit.
Admitted.

(** ** 基本的な演算です。 *)

(** 後者関数です。 *)

(* from: originally defined by Hexirp *)
Definition pred@{i | } : Nat@{i} -> Nat@{i} :=
  fix t (x : Nat@{i}) {struct x} : Nat@{i} :=
    match x with zero => zero | succ xp => t xp end.

(** 足し算です。 *)

(* from: originally defined by Hexirp *)
Definition add@{i | } : Nat@{i} -> Nat@{i} -> Nat@{i} :=
  fix t (x y : Nat@{i}) {struct x} : Nat@{i} :=
    match x with zero => y | succ xp => succ (t xp y) end.

(** 掛け算です。 *)

(* from: originally defined by Hexirp *)
Definition mul@{i | } : Nat@{i} -> Nat@{i} -> Nat@{i} :=
  fix t (x y : Nat@{i}) {struct x} : Nat@{i} :=
    match x with zero => y | succ xp => add y (t xp y) end.

(** 引き算です。 [sub x y] は [x + n = y + m] を満たすペア [m, n] の中で [m] が最大であるものです。 *)

(* from: originally defined by Hexirp *)
Definition sub@{i | } : Nat@{i} -> Nat@{i} -> Prod@{i i} Nat@{i} Nat@{i} :=
  fix t (x y : Nat@{i}) {struct x} : Prod@{i i} Nat@{i} Nat@{i} :=
    match x
      with
        | zero => pair zero@{i} y
        | succ xp =>
          match y
            with
              | zero => pair x zero@{i}
              | succ yp => t xp yp
          end
    end.

(** 割り算です。 [div x y] は [x = y * m + n] を満たすペア [m, n] の中で [m] が最大であるものです。 *)

(* from: originally defined by Hexirp *)
Definition div@{i | }
  : DSum Nat@{i} (fun x => IsTrue (lt zero x)) ->
    Nat@{i} -> Prod@{i i} Nat@{i} Nat@{i}.
Proof.
Admitted.
