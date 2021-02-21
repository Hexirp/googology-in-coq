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

(** ** 一般的な述語です。 *)

(** [y] は [x] 以上であることです。 *)

(* from: originally defined by Hexirp *)
Inductive Le@{i | } (x : Nat@{i}) (y : Nat@{i}) : Type@{i} :=
  | le_zero : Path@{i} x y -> Le x y
  | le_succ
    : forall yp : Nat@{i}, Path@{i} y (succ yp) -> Le x yp -> Le x y.

(** [y] は [x] より大きいことです。 *)

(* from: originally defined by Hexirp *)
Definition Lt@{i | } (x y : Nat@{i}) : Type@{i} := Le@{i} (succ x) y.

(** ** 一般的な演算です。 *)

(** 後者関数です。 *)

(* from: originally defined by Hexirp *)
Definition pred@{i | } : Nat@{i} -> Nat@{i} :=
  fix t (x : Nat@{i}) {struct x} : Nat@{i} :=
    match x with zero => zero | succ xp => t xp end.

(** 足し算です。 *)

(* from: originally defined by Hexirp *)
Definition add@{i | } : Nat@{i} -> Nat@{i} -> Nat@{i} :=
  fix t (x : Nat@{i}) (y : Nat@{i}) {struct x} : Nat@{i} :=
    match x with zero => y | succ xp => succ (t xp y) end.

(** 掛け算です。 *)

(* from: originally defined by Hexirp *)
Definition mul@{i | } : Nat@{i} -> Nat@{i} -> Nat@{i} :=
  fix t (x : Nat@{i}) (y : Nat@{i}) {struct x} : Nat@{i} :=
    match x with zero => y | succ xp => add y (t xp y) end.

(** 引き算です。 [sub x y] は [x + n = y + m] を満たすペア [m, n] の中で [m] が最大であるものです。 *)

(* from: originally defined by Hexirp *)
Definition sub@{i | } : Nat@{i} -> Nat@{i} -> Prod@{i i} Nat@{i} Nat@{i} :=
  fix t (x : Nat@{i}) (y : Nat@{i}) {struct x} : Prod@{i i} Nat@{i} Nat@{i} :=
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
Axiom div@{i | }
  : DSum Nat@{i} (fun x => Lt zero x) -> Nat@{i} -> Prod@{i i} Nat@{i} Nat@{i}.
