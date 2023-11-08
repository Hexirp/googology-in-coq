(** Playground モジュールは、まだ単独のモジュールに分割していないコードを置く場所です。 *)

Require Googology_In_Coq.Base.

Import Googology_In_Coq.Base.

(** ペアノ式の自然数を定義します。 *)

Inductive 数_自然_ペアノ@{ i | } : Type@{ i } := 零_数_自然_ペアノ : 数_自然_ペアノ | 次ぐ_数_自然_ペアノ : 数_自然_ペアノ -> 数_自然_ペアノ.

(** ペアノ式の自然数の 1 を定義します。 *)

Definition 一_数_自然_ペアノ@{ i | } : 数_自然_ペアノ@{ i } := 次ぐ_数_自然_ペアノ 零_数_自然_ペアノ.

(** ペアノ式の自然数の 2 を定義します。 *)

Definition 二_数_自然_ペアノ@{ i | } : 数_自然_ペアノ@{ i } := 次ぐ_数_自然_ペアノ 一_数_自然_ペアノ.

(** ペアノ式の自然数の 3 を定義します。 *)

Definition 三_数_自然_ペアノ@{ i | } : 数_自然_ペアノ@{ i } := 次ぐ_数_自然_ペアノ 二_数_自然_ペアノ.

(** ペアノ式の自然数の 4 を定義します。 *)

Definition 四_数_自然_ペアノ@{ i | } : 数_自然_ペアノ@{ i } := 次ぐ_数_自然_ペアノ 三_数_自然_ペアノ.

(** ペアノ式の自然数の 5 を定義します。 *)

Definition 五_数_自然_ペアノ@{ i | } : 数_自然_ペアノ@{ i } := 次ぐ_数_自然_ペアノ 四_数_自然_ペアノ.

(** ペアノ式の自然数の 6 を定義します。 *)

Definition 六_数_自然_ペアノ@{ i | } : 数_自然_ペアノ@{ i } := 次ぐ_数_自然_ペアノ 五_数_自然_ペアノ.

(** ペアノ式の自然数の 7 を定義します。 *)

Definition 七_数_自然_ペアノ@{ i | } : 数_自然_ペアノ@{ i } := 次ぐ_数_自然_ペアノ 六_数_自然_ペアノ.

(** ペアノ式の自然数の 8 を定義します。 *)

Definition 八_数_自然_ペアノ@{ i | } : 数_自然_ペアノ@{ i } := 次ぐ_数_自然_ペアノ 七_数_自然_ペアノ.

(** ペアノ式の自然数の 9 を定義します。 *)

Definition 九_数_自然_ペアノ@{ i | } : 数_自然_ペアノ@{ i } := 次ぐ_数_自然_ペアノ 八_数_自然_ペアノ.

(** ペアノ式の自然数の 10 を定義します。 *)

Definition 十_数_自然_ペアノ@{ i | } : 数_自然_ペアノ@{ i } := 次ぐ_数_自然_ペアノ 九_数_自然_ペアノ.

(** ペアノ式の自然数の加算を定義します。 *)

Definition 足す_数_自然_ペアノ@{ i | } : 数_自然_ペアノ@{ i } -> 数_自然_ペアノ@{ i } -> 数_自然_ペアノ@{ i } := fix a ( x : 数_自然_ペアノ@{ i } ) ( y : 数_自然_ペアノ@{ i } ) { struct y } : 数_自然_ペアノ@{ i } := match y with 零_数_自然_ペアノ => x | 次ぐ_数_自然_ペアノ y_p => 次ぐ_数_自然_ペアノ (a x y_p) end.
