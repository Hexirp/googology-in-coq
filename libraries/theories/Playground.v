(** Playground モジュールは、まだ単独のモジュールに分割していないコードを置く場所です。 *)

Require Googology_In_Coq.Base.

Import Googology_In_Coq.Base.

(** 自然数を定義します。 *)

Inductive 数_自然@{ i | } : Type@{ i } := 一_数_自然 : 数_自然 | 足す_数_自然 : 数_自然 -> 数_自然 -> 数_自然.

(** 自然数の 2 を定義します。 *)

Definition 二_数_自然@{ i | } : 数_自然@{ i } := 足す_数_自然 一_数_自然 一_数_自然.

(** 自然数の 3 を定義します。 *)

Definition 三_数_自然@{ i | } : 数_自然@{ i } := 足す_数_自然 二_数_自然 一_数_自然.

(** 自然数の 4 を定義します。 *)

Definition 四_数_自然@{ i | } : 数_自然@{ i } := 足す_数_自然 二_数_自然 二_数_自然.

(** 自然数の 5 を定義します。 *)

Definition 五_数_自然@{ i | } : 数_自然@{ i } := 足す_数_自然 四_数_自然 一_数_自然.

(** 自然数の 6 を定義します。 *)

Definition 六_数_自然@{ i | } : 数_自然@{ i } := 足す_数_自然 四_数_自然 二_数_自然.

(** 自然数の 7 を定義します。 *)

Definition 七_数_自然@{ i | } : 数_自然@{ i } := 足す_数_自然 四_数_自然 三_数_自然.

(** 自然数の 8 を定義します。 *)

Definition 八_数_自然@{ i | } : 数_自然@{ i } := 足す_数_自然 四_数_自然 四_数_自然.

(** 自然数の 9 を定義します。 *)

Definition 九_数_自然@{ i | } : 数_自然@{ i } := 足す_数_自然 八_数_自然 一_数_自然.

(** 自然数の 10 を定義します。 *)

Definition 十_数_自然@{ i | } : 数_自然@{ i } := 足す_数_自然 八_数_自然 二_数_自然.

(** 自然数の後者を定義します。 *)

Definition 次ぐ_数_自然@{ i | } : 数_自然@{ i } -> 数_自然@{ i } := 足す_数_自然 一_数_自然.

(** 自然数の掛け算を定義します。 *)

Definition 掛ける_数_自然@{ i | } : 数_自然@{ i } -> 数_自然@{ i } -> 数_自然@{ i }
    :=
        fix a ( x : 数_自然@{ i } ) ( y : 数_自然@{ i } ) { struct y } : 数_自然@{ i }
            := match y with 一_数_自然 => x | 足す_数_自然 yl yr => 足す_数_自然 ( a x yl ) ( a x yr ) end
.

(** ペアノ式の自然数を定義します。 *)

Inductive 数_自然_ペアノ@{ i | } : Type@{ i }
    :=
        一_数_自然_ペアノ : 数_自然_ペアノ
        |
        次ぐ_数_自然_ペアノ : 数_自然_ペアノ -> 数_自然_ペアノ
.

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

Definition 足す_数_自然_ペアノ@{ i | } : 数_自然_ペアノ@{ i } -> 数_自然_ペアノ@{ i } -> 数_自然_ペアノ@{ i }
    :=
        fix a ( x : 数_自然_ペアノ@{ i } ) ( y : 数_自然_ペアノ@{ i } ) { struct y } : 数_自然_ペアノ@{ i }
            :=
                match y
                    with
                        一_数_自然_ペアノ => 次ぐ_数_自然_ペアノ x
                        |
                        次ぐ_数_自然_ペアノ y_p => 次ぐ_数_自然_ペアノ ( a x y_p )
                end
.

(** ペアノ式の自然数の乗算を定義します。 *)

Definition 掛ける_数_自然_ペアノ@{ i | } : 数_自然_ペアノ@{ i } -> 数_自然_ペアノ@{ i } -> 数_自然_ペアノ@{ i }
    :=
        fix a ( x : 数_自然_ペアノ@{ i } ) ( y : 数_自然_ペアノ@{ i } ) { struct y } : 数_自然_ペアノ@{ i }
            :=
                match y
                    with
                        一_数_自然_ペアノ => x
                        |
                        次ぐ_数_自然_ペアノ y_p => 足す_数_自然_ペアノ x ( a x y_p )
                end
.

(** ペアノ式の自然数の冪乗を定義します。 *)

Definition 計算する_冪乗_数_自然_ペアノ@{ i | }
    : 数_自然_ペアノ@{ i } -> 数_自然_ペアノ@{ i } -> 数_自然_ペアノ@{ i }
    :=
        fix a ( x : 数_自然_ペアノ@{ i } ) ( y : 数_自然_ペアノ@{ i } ) { struct y } : 数_自然_ペアノ@{ i }
            :=
                match y
                    with
                        一_数_自然_ペアノ => x
                        |
                        次ぐ_数_自然_ペアノ y_p => 掛ける_数_自然_ペアノ x ( a x y_p )
                end
.

(** ペアノ式の自然数の最小値を定義します。 *)

Definition 計算する_値_最小_数_自然_ペアノ@{ i | }
    : 数_自然_ペアノ@{ i } -> 数_自然_ペアノ@{ i } -> 数_自然_ペアノ@{ i }
    :=
        fix a ( x : 数_自然_ペアノ@{ i } ) ( y : 数_自然_ペアノ@{ i } ) { struct y } : 数_自然_ペアノ@{ i }
            :=
                match x
                    with
                        一_数_自然_ペアノ => 一_数_自然_ペアノ
                        |
                        次ぐ_数_自然_ペアノ x_p
                            =>
                                match y
                                    with
                                        一_数_自然_ペアノ => 一_数_自然_ペアノ
                                        |
                                        次ぐ_数_自然_ペアノ y_p => 次ぐ_数_自然_ペアノ ( a x_p y_p )
                                end
                end
.

(** ペアノ式の自然数の最大値を定義します。 *)

Definition 計算する_値_最大_数_自然_ペアノ@{ i | }
    : 数_自然_ペアノ@{ i } -> 数_自然_ペアノ@{ i } -> 数_自然_ペアノ@{ i }
    :=
        fix a ( x : 数_自然_ペアノ@{ i } ) ( y : 数_自然_ペアノ@{ i } ) { struct y } : 数_自然_ペアノ@{ i }
            :=
                match x
                    with
                        一_数_自然_ペアノ => y
                        |
                        次ぐ_数_自然_ペアノ x_p
                            =>
                                match y
                                    with
                                        一_数_自然_ペアノ => x
                                        |
                                        次ぐ_数_自然_ペアノ y_p => 次ぐ_数_自然_ペアノ ( a x_p y_p )
                                end
                end
.

(** ペアノ式の自然数の三角数を定義します。 *)

Definition 計算する_数_三角_数_自然_ペアノ@{ i | } : 数_自然_ペアノ@{ i } -> 数_自然_ペアノ@{ i }
    :=
        fix a ( x : 数_自然_ペアノ@{ i } ) { struct x } : 数_自然_ペアノ@{ i }
            :=
                match x
                    with
                        一_数_自然_ペアノ => 一_数_自然_ペアノ
                        |
                        次ぐ_数_自然_ペアノ x_p => 足す_数_自然_ペアノ x ( a x_p )
                end
.

(** ペアノ式の自然数の階乗を定義します。 *)

Definition 計算する_階乗_数_自然_ペアノ@{ i | } : 数_自然_ペアノ@{ i } -> 数_自然_ペアノ@{ i }
    :=
        fix a ( x : 数_自然_ペアノ@{ i } ) { struct x } : 数_自然_ペアノ@{ i }
            :=
                match x
                    with
                        一_数_自然_ペアノ => 一_数_自然_ペアノ
                        |
                        次ぐ_数_自然_ペアノ x_p => 掛ける_数_自然_ペアノ x ( a x_p )
                end
.

(** ペアノ式の自然数のフィボナッチ数列を定義します。 *)

Definition 計算する_列_数_フィボナッチ_数_自然_ペアノ@{ i | } : 数_自然_ペアノ@{ i } -> 数_自然_ペアノ@{ i }
    :=
        let
            fix a ( x : 数_自然_ペアノ@{ i } ) ( y : 数_自然_ペアノ@{ i } ) ( z : 数_自然_ペアノ@{ i } )
                { struct x }
                : 数_自然_ペアノ@{ i }
                :=
                    match x
                        with
                            一_数_自然_ペアノ => y
                            |
                            次ぐ_数_自然_ペアノ x_p => a x_p z ( 足す_数_自然_ペアノ z y )
                    end
        in
            fun x : 数_自然_ペアノ@{ i } => a x 一_数_自然_ペアノ 一_数_自然_ペアノ
.

(** 0 始まりのペアノ式の自然数を定義します。 *)

Inductive 数_自然_ペアノ_始まり_零@{ i | } : Type@{ i }
    :=
        零_数_自然_ペアノ_始まり_零 : 数_自然_ペアノ_始まり_零
        |
        次ぐ_数_自然_ペアノ_始まり_零 : 数_自然_ペアノ_始まり_零 -> 数_自然_ペアノ_始まり_零
.

(** 0 始まりのペアノ式の自然数の 1 を定義します。 *)

Definition 一_数_自然_ペアノ_始まり_零@{ i | } : 数_自然_ペアノ_始まり_零@{ i }
    := 次ぐ_数_自然_ペアノ_始まり_零 零_数_自然_ペアノ_始まり_零
.

(** 0 始まりのペアノ式の自然数の 2 を定義します。 *)

Definition 二_数_自然_ペアノ_始まり_零@{ i | } : 数_自然_ペアノ_始まり_零@{ i }
    := 次ぐ_数_自然_ペアノ_始まり_零 一_数_自然_ペアノ_始まり_零
.

(** 0 始まりのペアノ式の自然数の 3 を定義します。 *)

Definition 三_数_自然_ペアノ_始まり_零@{ i | } : 数_自然_ペアノ_始まり_零@{ i }
    := 次ぐ_数_自然_ペアノ_始まり_零 二_数_自然_ペアノ_始まり_零
.

(** 0 始まりのペアノ式の自然数の 4 を定義します。 *)

Definition 四_数_自然_ペアノ_始まり_零@{ i | } : 数_自然_ペアノ_始まり_零@{ i }
    := 次ぐ_数_自然_ペアノ_始まり_零 三_数_自然_ペアノ_始まり_零
.

(** 0 始まりのペアノ式の自然数の 5 を定義します。 *)

Definition 五_数_自然_ペアノ_始まり_零@{ i | } : 数_自然_ペアノ_始まり_零@{ i }
    := 次ぐ_数_自然_ペアノ_始まり_零 四_数_自然_ペアノ_始まり_零
.

(** 0 始まりのペアノ式の自然数の 6 を定義します。 *)

Definition 六_数_自然_ペアノ_始まり_零@{ i | } : 数_自然_ペアノ_始まり_零@{ i }
    := 次ぐ_数_自然_ペアノ_始まり_零 五_数_自然_ペアノ_始まり_零
.

(** 0 始まりのペアノ式の自然数の 7 を定義します。 *)

Definition 七_数_自然_ペアノ_始まり_零@{ i | } : 数_自然_ペアノ_始まり_零@{ i }
    := 次ぐ_数_自然_ペアノ_始まり_零 六_数_自然_ペアノ_始まり_零
.

(** 0 始まりのペアノ式の自然数の 8 を定義します。 *)

Definition 八_数_自然_ペアノ_始まり_零@{ i | } : 数_自然_ペアノ_始まり_零@{ i }
    := 次ぐ_数_自然_ペアノ_始まり_零 七_数_自然_ペアノ_始まり_零
.

(** 0 始まりのペアノ式の自然数の 9 を定義します。 *)

Definition 九_数_自然_ペアノ_始まり_零@{ i | } : 数_自然_ペアノ_始まり_零@{ i }
    := 次ぐ_数_自然_ペアノ_始まり_零 八_数_自然_ペアノ_始まり_零
.

(** 0 始まりのペアノ式の自然数の 10 を定義します。 *)

Definition 十_数_自然_ペアノ_始まり_零@{ i | } : 数_自然_ペアノ_始まり_零@{ i }
    := 次ぐ_数_自然_ペアノ_始まり_零 九_数_自然_ペアノ_始まり_零
.

(** 0 始まりのペアノ式の自然数の加算を定義します。 *)

Definition 足す_数_自然_ペアノ_始まり_零@{ i | }
    : 数_自然_ペアノ_始まり_零@{ i } -> 数_自然_ペアノ_始まり_零@{ i } -> 数_自然_ペアノ_始まり_零@{ i }
    :=
        fix a ( x : 数_自然_ペアノ_始まり_零@{ i } ) ( y : 数_自然_ペアノ_始まり_零@{ i } ) { struct y }
            : 数_自然_ペアノ_始まり_零@{ i }
            :=
                match y
                    with
                        零_数_自然_ペアノ_始まり_零 => x
                        |
                        次ぐ_数_自然_ペアノ_始まり_零 y_p => 次ぐ_数_自然_ペアノ_始まり_零 ( a x y_p )
                end
.

(** 0 始まりのペアノ式の自然数の乗算を定義します。 *)

Definition 掛ける_数_自然_ペアノ_始まり_零@{ i | }
    : 数_自然_ペアノ_始まり_零@{ i } -> 数_自然_ペアノ_始まり_零@{ i } -> 数_自然_ペアノ_始まり_零@{ i }
    :=
        fix a ( x : 数_自然_ペアノ_始まり_零@{ i } ) ( y : 数_自然_ペアノ_始まり_零@{ i } ) { struct y }
            : 数_自然_ペアノ_始まり_零@{ i }
            :=
                match y
                    with
                        零_数_自然_ペアノ_始まり_零 => 零_数_自然_ペアノ_始まり_零
                        |
                        次ぐ_数_自然_ペアノ_始まり_零 y_p => 足す_数_自然_ペアノ_始まり_零 x ( a x y_p )
                end
.

(** 0 始まりのペアノ式の自然数の冪乗を定義します。 *)

Definition 計算する_冪乗_数_自然_ペアノ_始まり_零@{ i | }
    : 数_自然_ペアノ_始まり_零@{ i } -> 数_自然_ペアノ_始まり_零@{ i } -> 数_自然_ペアノ_始まり_零@{ i }
    :=
        fix a ( x : 数_自然_ペアノ_始まり_零@{ i } ) ( y : 数_自然_ペアノ_始まり_零@{ i } ) { struct y }
            : 数_自然_ペアノ_始まり_零@{ i }
            :=
                match y
                    with
                        零_数_自然_ペアノ_始まり_零 => 一_数_自然_ペアノ_始まり_零
                        |
                        次ぐ_数_自然_ペアノ_始まり_零 y_p => 掛ける_数_自然_ペアノ_始まり_零 x ( a x y_p )
                end
.

(** 0 始まりのペアノ式の自然数の最小値を定義します。 *)

Definition 計算する_値_最小_数_自然_ペアノ_始まり_零@{ i | }
    : 数_自然_ペアノ_始まり_零@{ i } -> 数_自然_ペアノ_始まり_零@{ i } -> 数_自然_ペアノ_始まり_零@{ i }
    :=
        fix a ( x : 数_自然_ペアノ_始まり_零@{ i } ) ( y : 数_自然_ペアノ_始まり_零@{ i } ) { struct y }
            : 数_自然_ペアノ_始まり_零@{ i }
            :=
                match x
                    with
                        零_数_自然_ペアノ_始まり_零 => 零_数_自然_ペアノ_始まり_零
                        |
                        次ぐ_数_自然_ペアノ_始まり_零 x_p
                            =>
                                match y
                                    with
                                        零_数_自然_ペアノ_始まり_零 => 零_数_自然_ペアノ_始まり_零
                                        |
                                        次ぐ_数_自然_ペアノ_始まり_零 y_p => 次ぐ_数_自然_ペアノ_始まり_零 ( a x_p y_p )
                                end
                end
.

(** 0 始まりのペアノ式の自然数の最大値を定義します。 *)

Definition 計算する_値_最大_数_自然_ペアノ_始まり_零@{ i | }
    : 数_自然_ペアノ_始まり_零@{ i } -> 数_自然_ペアノ_始まり_零@{ i } -> 数_自然_ペアノ_始まり_零@{ i }
    :=
        fix a ( x : 数_自然_ペアノ_始まり_零@{ i } ) ( y : 数_自然_ペアノ_始まり_零@{ i } ) { struct y }
            : 数_自然_ペアノ_始まり_零@{ i }
            :=
                match x
                    with
                        零_数_自然_ペアノ_始まり_零 => y
                        |
                        次ぐ_数_自然_ペアノ_始まり_零 x_p
                            =>
                                match y
                                    with
                                        零_数_自然_ペアノ_始まり_零 => x
                                        |
                                        次ぐ_数_自然_ペアノ_始まり_零 y_p => 次ぐ_数_自然_ペアノ_始まり_零 ( a x_p y_p )
                                end
                end
.

(** 0 始まりのペアノ式の自然数の三角数を定義します。 *)

Definition 計算する_数_三角_数_自然_ペアノ_始まり_零@{ i | }
    : 数_自然_ペアノ_始まり_零@{ i } -> 数_自然_ペアノ_始まり_零@{ i }
    :=
        fix a ( x : 数_自然_ペアノ_始まり_零@{ i } ) { struct x } : 数_自然_ペアノ_始まり_零@{ i }
            :=
                match x
                    with
                        零_数_自然_ペアノ_始まり_零 => 零_数_自然_ペアノ_始まり_零
                        |
                        次ぐ_数_自然_ペアノ_始まり_零 x_p => 足す_数_自然_ペアノ_始まり_零 x ( a x_p )
                end
.

(** 0 始まりのペアノ式の自然数の階乗を定義します。 *)

Definition 計算する_階乗_数_自然_ペアノ_始まり_零@{ i | }
    : 数_自然_ペアノ_始まり_零@{ i } -> 数_自然_ペアノ_始まり_零@{ i }
    :=
        fix a ( x : 数_自然_ペアノ_始まり_零@{ i } ) { struct x } : 数_自然_ペアノ_始まり_零@{ i }
            :=
                match x
                    with
                        零_数_自然_ペアノ_始まり_零 => 一_数_自然_ペアノ_始まり_零
                        |
                        次ぐ_数_自然_ペアノ_始まり_零 x_p => 掛ける_数_自然_ペアノ_始まり_零 x ( a x_p )
                end
.

(** 0 始まりのペアノ式の自然数の二項係数を定義します。 *)

Definition 計算する_係数_二項_数_自然_ペアノ_始まり_零@{ i | }
    : 数_自然_ペアノ_始まり_零@{ i } -> 数_自然_ペアノ_始まり_零@{ i } -> 数_自然_ペアノ_始まり_零@{ i }
    :=
        fix a ( x : 数_自然_ペアノ_始まり_零@{ i } ) ( y : 数_自然_ペアノ_始まり_零@{ i } ) { struct x }
            : 数_自然_ペアノ_始まり_零@{ i }
            :=
                match x
                    with
                        零_数_自然_ペアノ_始まり_零
                            =>
                                match y
                                    with
                                        零_数_自然_ペアノ_始まり_零 => 一_数_自然_ペアノ_始まり_零
                                        |
                                        次ぐ_数_自然_ペアノ_始まり_零 y_p => 零_数_自然_ペアノ_始まり_零
                                end
                        |
                        次ぐ_数_自然_ペアノ_始まり_零 x_p
                            =>
                                match y
                                    with
                                        零_数_自然_ペアノ_始まり_零 => 一_数_自然_ペアノ_始まり_零
                                        |
                                        次ぐ_数_自然_ペアノ_始まり_零 y_p
                                            => 足す_数_自然_ペアノ_始まり_零 ( a x_p y ) ( a x_p y_p )
                                end
                end
.

(** 0 始まりのペアノ式の自然数のフィボナッチ数列を定義します。 *)

Definition 計算する_列_数_フィボナッチ_数_自然_ペアノ_始まり_零@{ i | }
    : 数_自然_ペアノ_始まり_零@{ i } -> 数_自然_ペアノ_始まり_零@{ i }
    :=
        let
            fix a
                ( x : 数_自然_ペアノ_始まり_零@{ i } )
                ( y : 数_自然_ペアノ_始まり_零@{ i } )
                ( z : 数_自然_ペアノ_始まり_零@{ i } )
                { struct x }
                : 数_自然_ペアノ_始まり_零@{ i }
                :=
                    match x
                        with
                            零_数_自然_ペアノ_始まり_零 => y
                            |
                            次ぐ_数_自然_ペアノ_始まり_零 x_p => a x_p z ( 足す_数_自然_ペアノ_始まり_零 z y )
                    end
        in
            fun x : 数_自然_ペアノ_始まり_零@{ i } => a x 零_数_自然_ペアノ_始まり_零 一_数_自然_ペアノ_始まり_零
.

(** 道の型を定義します。 *)

Inductive 道_0@{ i | } ( A : Type@{ i } ) ( a : A ) : A -> Type@{ i } := 道_0_恒等 : 道_0 A a a.

(** ペアノ式の自然数に関する関数を検算します。 *)

Check 道_0_恒等 _ _ : 道_0 数_自然_ペアノ (次ぐ_数_自然_ペアノ 一_数_自然_ペアノ) 二_数_自然_ペアノ.

Check 道_0_恒等 _ _ : 道_0 数_自然_ペアノ (足す_数_自然_ペアノ 三_数_自然_ペアノ 二_数_自然_ペアノ) 五_数_自然_ペアノ.

Check 道_0_恒等 _ _
    :
        道_0
            数_自然_ペアノ
            (掛ける_数_自然_ペアノ 三_数_自然_ペアノ 三_数_自然_ペアノ)
            九_数_自然_ペアノ
.

Check 道_0_恒等 _ _
    :
        道_0
            数_自然_ペアノ
            (計算する_冪乗_数_自然_ペアノ 二_数_自然_ペアノ 三_数_自然_ペアノ)
            八_数_自然_ペアノ
.

Check 道_0_恒等 _ _ : 道_0 数_自然_ペアノ (計算する_数_三角_数_自然_ペアノ 四_数_自然_ペアノ) 十_数_自然_ペアノ.

Check 道_0_恒等 _ _
    :
        道_0
            数_自然_ペアノ
            (計算する_階乗_数_自然_ペアノ 四_数_自然_ペアノ)
            (掛ける_数_自然_ペアノ 六_数_自然_ペアノ 四_数_自然_ペアノ)
.

Check 道_0_恒等 _ _
    :
        道_0
            数_自然_ペアノ
            (計算する_列_数_フィボナッチ_数_自然_ペアノ 八_数_自然_ペアノ)
            (掛ける_数_自然_ペアノ 七_数_自然_ペアノ 三_数_自然_ペアノ)
.

(** 0 始まりのペアノ式の自然数に関する関数を検算します。 *)

Check 道_0_恒等 _ _
    :
        道_0
            数_自然_ペアノ_始まり_零
                (次ぐ_数_自然_ペアノ_始まり_零 零_数_自然_ペアノ_始まり_零)
                一_数_自然_ペアノ_始まり_零
.

Check 道_0_恒等 _ _
    :
        道_0
            数_自然_ペアノ_始まり_零
                (足す_数_自然_ペアノ_始まり_零 三_数_自然_ペアノ_始まり_零 二_数_自然_ペアノ_始まり_零)
                五_数_自然_ペアノ_始まり_零
.

Check 道_0_恒等 _ _
    :
        道_0
            数_自然_ペアノ_始まり_零
                (掛ける_数_自然_ペアノ_始まり_零 三_数_自然_ペアノ_始まり_零 三_数_自然_ペアノ_始まり_零)
                九_数_自然_ペアノ_始まり_零
.

Check 道_0_恒等 _ _
    :
        道_0
            数_自然_ペアノ_始まり_零
                (計算する_冪乗_数_自然_ペアノ_始まり_零 二_数_自然_ペアノ_始まり_零 三_数_自然_ペアノ_始まり_零)
                八_数_自然_ペアノ_始まり_零
.

Check 道_0_恒等 _ _
    :
        道_0
            数_自然_ペアノ_始まり_零
                (計算する_数_三角_数_自然_ペアノ_始まり_零 四_数_自然_ペアノ_始まり_零)
                十_数_自然_ペアノ_始まり_零
.

Check 道_0_恒等 _ _
    :
        道_0
            数_自然_ペアノ_始まり_零
            (計算する_階乗_数_自然_ペアノ_始まり_零 四_数_自然_ペアノ_始まり_零)
            (掛ける_数_自然_ペアノ_始まり_零 六_数_自然_ペアノ_始まり_零 四_数_自然_ペアノ_始まり_零)
.

Check 道_0_恒等 _ _
    :
        道_0
            数_自然_ペアノ_始まり_零
            (計算する_係数_二項_数_自然_ペアノ_始まり_零 八_数_自然_ペアノ_始まり_零 四_数_自然_ペアノ_始まり_零)
            (掛ける_数_自然_ペアノ_始まり_零 十_数_自然_ペアノ_始まり_零 七_数_自然_ペアノ_始まり_零)
.

Check 道_0_恒等 _ _
    :
        道_0
            数_自然_ペアノ_始まり_零
            (計算する_列_数_フィボナッチ_数_自然_ペアノ_始まり_零 八_数_自然_ペアノ_始まり_零)
            (掛ける_数_自然_ペアノ_始まり_零 七_数_自然_ペアノ_始まり_零 三_数_自然_ペアノ_始まり_零)
.

(** 道の結合を定義します。 *)

Definition 結合する_道_0@{ i | }
    ( A : Type@{ i } )
    ( x : A )
    ( y : A )
    ( z : A )
    ( p : 道_0 A x y )
    ( q : 道_0 A y z )
    : 道_0 A x z
    := match q in 道_0 _ _ z_ return 道_0 A x z_ with 道_0_恒等 _ _ => p end
.

(** 道の反転を定義します。 *)

Definition 反転する_道_0@{ i | } ( A : Type@{ i } ) ( x : A ) ( y : A ) ( p : 道_0 A x y ) : 道_0 A y x
    := match p in 道_0 _ _ y_ return 道_0 A y_ x with 道_0_恒等 _ _ => 道_0_恒等 A x end
.

(** 道への関数適用を定義します。 *)

Definition 適用する_関数_道_0@{ i | }
    ( A : Type@{ i } )
    ( B : Type@{ i } )
    ( f : A -> B )
    ( x : A )
    ( y : A )
    ( p : 道_0 A x y )
    : 道_0 B ( f x ) ( f y )
    := match p in 道_0 _ _ y_ return 道_0 B ( f x ) ( f y_ ) with 道_0_恒等 _ _ => 道_0_恒等 B ( f x ) end
.

(** ペアノ式の自然数における加算についての右の基の場合における性質の補題を証明します。 *)

Definition 補題_場合_基_右_足す_数_自然_ペアノ@{ i | } ( m : 数_自然_ペアノ@{ i } )
    : 道_0 数_自然_ペアノ ( 足す_数_自然_ペアノ m 一_数_自然_ペアノ ) ( 次ぐ_数_自然_ペアノ m )
    := 道_0_恒等 _ _
.

(** ペアノ式の自然数における加算についての左の基の場合における値の補題を証明します。 *)

Definition 補題_場合_基_左_足す_数_自然_ペアノ@{ i | } ( n : 数_自然_ペアノ@{ i } )
    : 道_0 数_自然_ペアノ ( 足す_数_自然_ペアノ 一_数_自然_ペアノ n ) ( 次ぐ_数_自然_ペアノ n )
    :=
        let
            fix a ( n_ : 数_自然_ペアノ@{ i } ) { struct n_ }
                : 道_0 数_自然_ペアノ ( 足す_数_自然_ペアノ 一_数_自然_ペアノ n_ ) ( 次ぐ_数_自然_ペアノ n_ )
                :=
                    match n_
                        as n__
                        return 道_0 数_自然_ペアノ ( 足す_数_自然_ペアノ 一_数_自然_ペアノ n__ ) ( 次ぐ_数_自然_ペアノ n__ )
                        with
                            一_数_自然_ペアノ => 道_0_恒等 _ _
                            |
                            次ぐ_数_自然_ペアノ n_p
                                =>
                                    適用する_関数_道_0
                                        _
                                        _
                                        次ぐ_数_自然_ペアノ
                                        ( 足す_数_自然_ペアノ 一_数_自然_ペアノ n_p )
                                        ( 次ぐ_数_自然_ペアノ n_p )
                                        ( a n_p )
                    end
        in
            a n
.

(** ペアノ式の自然数における加算についての右の段の場合における性質の補題を証明します。 *)

Definition 補題_場合_段_右_足す_数_自然_ペアノ@{ i | } ( m : 数_自然_ペアノ@{ i } ) ( n : 数_自然_ペアノ@{ i } )
    :
        道_0
            数_自然_ペアノ
            ( 足す_数_自然_ペアノ m ( 次ぐ_数_自然_ペアノ n ) )
            ( 次ぐ_数_自然_ペアノ ( 足す_数_自然_ペアノ m n ) )
    := 道_0_恒等 _ _
.

(** ペアノ式の自然数における加算についての左の段の場合における値の補題を証明します。 *)

Definition 補題_場合_段_左_足す_数_自然_ペアノ@{ i | } ( m : 数_自然_ペアノ@{ i } ) ( n : 数_自然_ペアノ@{ i } )
    :
        道_0
            数_自然_ペアノ
            ( 足す_数_自然_ペアノ ( 次ぐ_数_自然_ペアノ m ) n )
            ( 次ぐ_数_自然_ペアノ ( 足す_数_自然_ペアノ m n ) )
    :=
        let
            fix a ( n_ : 数_自然_ペアノ@{ i } ) { struct n_ }
                :
                    道_0
                        数_自然_ペアノ
                        ( 足す_数_自然_ペアノ ( 次ぐ_数_自然_ペアノ m ) n_ )
                        ( 次ぐ_数_自然_ペアノ ( 足す_数_自然_ペアノ m n_ ) )
                :=
                    match n_
                        as n__
                        return
                            道_0
                                数_自然_ペアノ
                                ( 足す_数_自然_ペアノ ( 次ぐ_数_自然_ペアノ m ) n__ )
                                ( 次ぐ_数_自然_ペアノ ( 足す_数_自然_ペアノ m n__ ) )
                        with
                            一_数_自然_ペアノ => 道_0_恒等 _ _
                            |
                            次ぐ_数_自然_ペアノ n_p
                                =>
                                    適用する_関数_道_0
                                        _
                                        _
                                        次ぐ_数_自然_ペアノ
                                        ( 足す_数_自然_ペアノ ( 次ぐ_数_自然_ペアノ m ) n_p )
                                        ( 次ぐ_数_自然_ペアノ ( 足す_数_自然_ペアノ m n_p ) )
                                        ( a n_p )
                    end
        in
            a n
.

(** 自然数を定義する。 *)

Inductive 自然数@{ i | } : Type@{i}
    :=
        零_構築子_自然数 : 自然数
        |
        後者_構築子_自然数 : 自然数 -> 自然数
.

Definition 零_自然数@{ i | } : 自然数@{ i } := 零_構築子_自然数.

Definition 一_自然数@{ i | } : 自然数@{ i } := 後者_構築子_自然数 零_自然数.

Definition 二_自然数@{ i | } : 自然数@{ i } := 後者_構築子_自然数 一_自然数.

Definition 三_自然数@{ i | } : 自然数@{ i } := 後者_構築子_自然数 二_自然数.

Definition 四_自然数@{ i | } : 自然数@{ i } := 後者_構築子_自然数 三_自然数.

Definition 五_自然数@{ i | } : 自然数@{ i } := 後者_構築子_自然数 四_自然数.

Definition 六_自然数@{ i | } : 自然数@{ i } := 後者_構築子_自然数 五_自然数.

Definition 七_自然数@{ i | } : 自然数@{ i } := 後者_構築子_自然数 六_自然数.

Definition 八_自然数@{ i | } : 自然数@{ i } := 後者_構築子_自然数 七_自然数.

Definition 九_自然数@{ i | } : 自然数@{ i } := 後者_構築子_自然数 八_自然数.

Definition 十_自然数@{ i | } : 自然数@{ i } := 後者_構築子_自然数 九_自然数.

Definition 後者を計算する_自然数@{ i | } : 自然数@{ i } -> 自然数@{ i } := 後者_構築子_自然数.

Definition 足す_自然数@{ i | } : 自然数@{ i } -> 自然数@{ i } -> 自然数@{ i }
    :=
        fix a ( x : 自然数@{ i } ) ( y : 自然数@{ i } ) { struct x } : 自然数@{ i }
            :=
                match
                    x
                with
                    零_構築子_自然数
                        =>
                            match
                                y
                            with
                                零_構築子_自然数 => 零_自然数
                                |
                                後者_構築子_自然数 y_p => 後者_構築子_自然数 y_p
                            end
                    |
                    後者_構築子_自然数 x_p
                        =>
                            match
                                y
                            with
                                零_構築子_自然数 => 後者_構築子_自然数 x_p
                                |
                                後者_構築子_自然数 y_p => 後者_構築子_自然数 ( 後者_構築子_自然数 ( a x_p y_p ) )
                            end
                end
.

Definition 掛ける_自然数@{ i | } : 自然数@{ i } -> 自然数@{ i } -> 自然数@{ i }
    :=
        fix a ( x : 自然数@{ i } ) ( y : 自然数@{ i } ) { struct y } : 自然数@{ i }
            :=
                match
                    y
                with
                    零_構築子_自然数 => 零_自然数
                    |
                    後者_構築子_自然数 y_p => 足す_自然数 x ( a x y_p )
                end
.

Definition 冪乗を計算する_自然数@{ i | } : 自然数@{ i } -> 自然数@{ i } -> 自然数@{ i }
    :=
        fix a ( x : 自然数@{ i } ) ( y : 自然数@{ i } ) { struct y } : 自然数@{ i }
            :=
                match
                    y
                with
                    零_構築子_自然数 => 零_自然数
                    |
                    後者_構築子_自然数 y_p => 掛ける_自然数 x ( a x y_p )
                end
.

(** 道を定義する。「道」は "path" の訳語である。 *)

Inductive 道@{ i | } ( A : Type@{ i } ) ( x : A ) : A -> Type@{ i } := 構築子_道 : 道 A x x.

(** 「恒等道」は "identity path" の訳語である。 *)

Definition 恒等道_道@{ i | } ( A : Type@{ i } ) ( x : A ) : 道 A x x := 構築子_道 A x.

Definition 結合する_道@{ i | }
    ( A : Type@{ i } )
    ( x : A )
    ( y : A )
    ( z : A )
    ( p : 道 A x y )
    ( q : 道 A y z )
    : 道 A x z
    :=
        let
            a
                :=
                    match
                        p
                    in
                        道 _ _ y_
                    return
                        道 A y_ z -> 道 A x z
                    with
                        構築子_道 _ _
                            =>
                                fun q_ : 道 A x z =>
                                    match
                                        q_
                                    in
                                        道 _ _ z_
                                    return
                                        道 A x z_
                                    with
                                        構築子_道 _ _ => 構築子_道 A x
                                    end
                    end
        in
            a q
.

Definition A_2024_01_24_0000@{ i | } : 道@{ i } 自然数@{ i } ( 後者を計算する_自然数 八_自然数 ) 九_自然数 := 恒等道_道 _ _.

Definition A_2024_01_24_0001@{ i | } : 道@{ i } 自然数@{ i } ( 足す_自然数 三_自然数 二_自然数 ) 五_自然数 := 恒等道_道 _ _.

Definition A_2024_01_24_0002@{ i | } : 道@{ i } 自然数@{ i } ( 掛ける_自然数 三_自然数 三_自然数 ) 九_自然数
    := 恒等道_道 _ _
.

Definition A_2024_01_24_0003@{ i | } : 道@{ i } 自然数@{ i } ( 冪乗を計算する_自然数 二_自然数 三_自然数 ) 八_自然数
    := 恒等道_道 _ _
.
