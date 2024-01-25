(** Playground モジュールは、まだ単独のモジュールに分割していないコードを置く場所です。 *)

Require Googology_In_Coq.Base.

Import Googology_In_Coq.Base.

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
                    零_構築子_自然数 => 一_自然数
                    |
                    後者_構築子_自然数 y_p => 掛ける_自然数 x ( a x y_p )
                end
.

Definition 最小値を計算する_自然数@{ i | } : 自然数@{ i } -> 自然数@{ i } -> 自然数@{ i }
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
                                後者_構築子_自然数 y_p => 零_自然数
                            end
                    |
                    後者_構築子_自然数 x_p
                        =>
                            match
                                y
                            with
                                零_構築子_自然数 => 零_自然数
                                |
                                後者_構築子_自然数 y_p => 後者_構築子_自然数 ( a x_p y_p )
                            end
                end
.

Definition 最大値を計算する_自然数@{ i | } : 自然数@{ i } -> 自然数@{ i } -> 自然数@{ i }
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
                                後者_構築子_自然数 y_p => 後者_構築子_自然数 ( a x_p y_p )
                            end
                end
.

Definition 三角数を計算する_自然数@{ i | } : 自然数@{ i } -> 自然数@{ i }
    :=
        fix a ( x : 自然数@{ i } ) { struct x } : 自然数@{ i }
            :=
                match
                    x
                with
                    零_構築子_自然数 => 零_自然数
                    |
                    後者_構築子_自然数 x_p => 足す_自然数 x ( a x_p )
                end
.

Definition 階乗を計算する_自然数@{ i | } : 自然数@{ i } -> 自然数@{ i }
    :=
        fix a ( x : 自然数@{ i } ) { struct x } : 自然数@{ i }
            :=
                match
                    x
                with
                    零_構築子_自然数 => 一_自然数
                    |
                    後者_構築子_自然数 x_p => 掛ける_自然数 x ( a x_p )
                end
.

Definition 二項係数を計算する_自然数@{ i | } : 自然数@{ i } -> 自然数@{ i } -> 自然数@{ i }
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
                                零_構築子_自然数 => 一_自然数
                                |
                                後者_構築子_自然数 y_p => 零_自然数
                            end
                    |
                    後者_構築子_自然数 x_p
                        =>
                            match
                                y
                            with
                                零_構築子_自然数 => 一_自然数
                                |
                                後者_構築子_自然数 y_p => 足す_自然数 ( a x_p y ) ( a x_p y_p )
                        end
                end
.

Definition フィボナッチ数を計算する_自然数@{ i | } : 自然数@{ i } -> 自然数@{ i }
    :=
        let
            fix a ( x : 自然数@{ i } ) ( y : 自然数@{ i } ) ( z : 自然数@{ i } ) { struct x } : 自然数@{ i }
                :=
                    match
                        x
                    with
                        零_構築子_自然数 => y
                        |
                        後者_構築子_自然数 x_p => a x_p z ( 足す_自然数 y z )
                    end
        in
            fun x : 自然数@{ i } => a x 零_自然数 一_自然数
.

(** 空型を定義します。「空型」は "empty type" の訳語です。 *)

Inductive 空型@{ i | } : Type@{ i } :=.

Definition 不条理である_空型@{ i j | } ( A : Type@{ i } ) ( x : 空型@{ j } ) : A := match x with end.

(** 否定を定義します。 *)

Definition 否定@{ i | } ( A : Type@{ i } ) : Type@{ i } := A -> 空型@{ i }.

Definition A_2024_01_26_0000@{ i j | } ( A : Type@{ i } ) ( B : Type@{ j } ) ( f : A -> B ) : 否定@{ j } B -> 否定@{ i } A
    := fun x : 否定@{ j } B => fun y : A => x ( f y )
.

(** 直和型を定義します。 *)

Inductive 直和@{ i | } ( A : Type@{ i } ) ( B : Type@{ i } ) : Type@{ i }
    := 左_構築子_直和 : A -> 直和 A B | 右_構築子_直和 : B -> 直和 A B
.

Definition A_2024_01_26_0001@{ i | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( e : 否定@{ i } B ) ( x : 直和@{ i } A B ) : A
    := match x with 左_構築子_直和 _ _ x_l => x_l | 右_構築子_直和 _ _ x_r => 不条理である_空型 A ( e x_r ) end
.

Definition A_2024_01_26_0002@{ i | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( e : 否定@{ i } A ) ( x : 直和@{ i } A B ) : B
    := match x with 左_構築子_直和 _ _ x_l => 不条理である_空型 B ( e x_l ) | 右_構築子_直和 _ _ x_r => x_r end
.

(** 道を定義する。「道」は "path" の訳語である。 *)

Inductive 道@{ i | } ( A : Type@{ i } ) ( x : A ) : A -> Type@{ i } := 構築子_道 : 道 A x x.

(** 「恒等道」は "identity path" の訳語である。 *)

Definition 恒等道_道@{ i | } ( A : Type@{ i } ) ( x : A ) : 道 A x x := 構築子_道 A x.

Definition 結合する_道@{ i | } ( A : Type@{ i } ) ( x : A ) ( y : A ) ( z : A ) ( p : 道 A x y ) ( q : 道 A y z )
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
                                    match q_ in 道 _ _ z_ return 道 A x z_ with 構築子_道 _ _ => 構築子_道 A x end
                    end
        in
            a q
.

Definition 反転する_道@{ i | } ( A : Type@{ i } ) ( x : A ) ( y : A ) ( p : 道 A x y ) : 道 A y x
    := match p in 道 _ _ y_ return 道 A y_ x with 構築子_道 _ _ => 構築子_道 A x end
.

Definition 関数を適用する_道@{ i j | }
        ( A : Type@{ i } )
        ( B : Type@{ j } )
        ( f : A -> B )
        ( x : A )
        ( y : A )
        ( p : 道 A x y )
    : 道 B ( f x ) ( f y )
    := match p in 道 _ _ y_ return 道 B ( f x ) ( f y_ ) with 構築子_道 _ _ => 構築子_道 B ( f x ) end
.

Definition A_2024_01_24_0000@{ i | } : 道@{ i } 自然数@{ i } ( 後者を計算する_自然数 八_自然数 ) 九_自然数
    := 恒等道_道 _ _
.

Definition A_2024_01_24_0001@{ i | } : 道@{ i } 自然数@{ i } ( 足す_自然数 三_自然数 二_自然数 ) 五_自然数
    := 恒等道_道 _ _
.

Definition A_2024_01_24_0002@{ i | } : 道@{ i } 自然数@{ i } ( 掛ける_自然数 三_自然数 三_自然数 ) 九_自然数
    := 恒等道_道 _ _
.

Definition A_2024_01_24_0003@{ i | } : 道@{ i } 自然数@{ i } ( 冪乗を計算する_自然数 二_自然数 三_自然数 ) 八_自然数
    := 恒等道_道 _ _
.

Definition A_2024_01_24_0004@{ i | } : 道@{ i } 自然数@{ i } ( 最小値を計算する_自然数 八_自然数 七_自然数 ) 七_自然数
    := 恒等道_道 _ _
.

Definition A_2024_01_24_0005@{ i | } : 道@{ i } 自然数@{ i } ( 最大値を計算する_自然数 五_自然数 六_自然数 ) 六_自然数
    := 恒等道_道 _ _
.

Definition A_2024_01_24_0006@{ i | } : 道@{ i } 自然数@{ i } ( 三角数を計算する_自然数 四_自然数 ) 十_自然数
    := 恒等道_道 _ _
.

Definition A_2024_01_24_0007@{ i | }
    : 道@{ i } 自然数@{ i } ( 階乗を計算する_自然数 四_自然数 ) ( 掛ける_自然数 六_自然数 四_自然数 )
    := 恒等道_道 _ _
.

Definition A_2024_01_24_0008@{ i | }
    : 道@{ i } 自然数@{ i } ( 二項係数を計算する_自然数 八_自然数 四_自然数 ) ( 掛ける_自然数 十_自然数 七_自然数 )
    := 恒等道_道 _ _
.

Definition A_2024_01_24_0009@{ i | }
    : 道@{ i } 自然数@{ i } ( フィボナッチ数を計算する_自然数 八_自然数 ) ( 掛ける_自然数 七_自然数 三_自然数 )
    := 恒等道_道 _ _
.

Definition A_2024_01_25_0000@{ i | } ( m : 自然数@{ i } ) : 道 自然数 ( 足す_自然数 m 零_自然数 ) m
    :=
        match
            m
        as
            m_
        return
            道 自然数@{ i } ( 足す_自然数 m_ 零_自然数 ) m_
        with
            零_構築子_自然数 => 恒等道_道 自然数@{ i } 零_自然数
            |
            後者_構築子_自然数 m_p => 恒等道_道 自然数@{ i } ( 後者を計算する_自然数 m_p )
        end
.

Definition A_2024_01_25_0001@{ i | } ( n : 自然数@{ i } ) : 道 自然数 ( 足す_自然数 零_自然数 n ) n
    :=
        match
            n
        as
            n_
        return
            道 自然数@{ i } ( 足す_自然数 零_自然数 n_ ) n_
        with
            零_構築子_自然数 => 恒等道_道 自然数@{ i } 零_自然数
            |
            後者_構築子_自然数 n_p => 恒等道_道 自然数@{ i } ( 後者を計算する_自然数 n_p )
        end
.

Definition A_2024_01_25_0002@{ i | } ( m : 自然数@{ i } ) ( n : 自然数@{ i } )
    : 道@{ i } 自然数@{ i } ( 足す_自然数 m ( 後者を計算する_自然数 n ) ) ( 後者を計算する_自然数 ( 足す_自然数 m n ) )
.
Proof.
    refine ( let a := _ in a m n ).
    refine
        (
            fix a ( m : 自然数@{ i } ) ( n : 自然数@{ i } ) { struct m }
                :
                    道@{ i }
                        自然数@{ i }
                        ( 足す_自然数 m ( 後者を計算する_自然数 n ) )
                        ( 後者を計算する_自然数 ( 足す_自然数 m n ) )
                := _
        )
    .
    refine
        (
            match
                m
            as
                m_
            return
                道@{ i }
                    自然数@{ i }
                    ( 足す_自然数 m_ ( 後者を計算する_自然数 n ) )
                    ( 後者を計算する_自然数 ( 足す_自然数 m_ n ) )
            with
                零_構築子_自然数 => _
                |
                後者_構築子_自然数 m_p => _
            end
        )
    .
    -
        refine
            (
                match
                    n
                as
                    n_
                return
                    道@{ i }
                        自然数@{ i }
                        ( 足す_自然数 零_自然数 ( 後者を計算する_自然数 n_ ) )
                        ( 後者を計算する_自然数 ( 足す_自然数 零_自然数 n_ ) )
                with
                    零_構築子_自然数 => _
                    |
                    後者_構築子_自然数 n_p => _
                end
            )
        .
        +
            change
                (
                    道@{ i }
                        自然数@{ i }
                        ( 足す_自然数 零_自然数 ( 後者を計算する_自然数 零_自然数 ) )
                        ( 後者を計算する_自然数 ( 足す_自然数 零_自然数 零_自然数 ) )
                )
            .
            change ( 道@{ i } 自然数@{ i } ( 後者を計算する_自然数 零_自然数 ) ( 後者を計算する_自然数 零_自然数 ) ).
            exact ( 恒等道_道 自然数@{ i } ( 後者を計算する_自然数 零_自然数 ) ).
        +
            change
                (
                    道@{ i }
                        自然数@{ i }
                        ( 足す_自然数 零_自然数 ( 後者を計算する_自然数 ( 後者を計算する_自然数 n_p ) ) )
                        ( 後者を計算する_自然数 ( 足す_自然数 零_自然数 ( 後者を計算する_自然数 n_p ) ) )
                )
            .
            change
                (
                    道@{ i }
                        自然数@{ i }
                        ( 後者を計算する_自然数 ( 後者を計算する_自然数 n_p ) )
                        ( 後者を計算する_自然数 ( 後者を計算する_自然数 n_p ) )
                )
            .
            exact ( 恒等道_道 自然数@{ i } ( 後者を計算する_自然数 ( 後者を計算する_自然数 n_p ) ) ).
    -
        refine
            (
                match
                    n
                as
                    n_
                return
                    道@{ i }
                        自然数@{ i }
                        ( 足す_自然数 ( 後者を計算する_自然数 m_p ) ( 後者を計算する_自然数 n_ ) )
                        ( 後者を計算する_自然数 ( 足す_自然数 ( 後者を計算する_自然数 m_p ) n_ ) )
                with
                    零_構築子_自然数 => _
                    |
                    後者_構築子_自然数 n_p => _
                end
            )
        .
        +
            change
                (
                    道@{ i }
                        自然数@{ i }
                        ( 足す_自然数 ( 後者を計算する_自然数 m_p ) ( 後者を計算する_自然数 零_自然数 ) )
                        ( 後者を計算する_自然数 ( 足す_自然数 ( 後者を計算する_自然数 m_p ) 零_自然数 ) )
                )
            .
            change
                (
                    道@{ i }
                        自然数@{ i }
                        ( 後者を計算する_自然数 ( 後者を計算する_自然数 ( 足す_自然数 m_p 零_自然数 ) ) )
                        ( 後者を計算する_自然数 ( 後者を計算する_自然数 m_p ) )
                )
            .
            refine
                (
                    関数を適用する_道
                        自然数@{ i }
                        自然数@{ i }
                        ( fun x : 自然数@{ i } => 後者を計算する_自然数 ( 後者を計算する_自然数 x ) )
                        ( 足す_自然数 m_p 零_自然数 )
                        m_p
                        _
                )
            .
            exact ( A_2024_01_25_0000 m_p ).
        +
            change
                (
                    道@{ i }
                        自然数@{ i }
                        (
                            足す_自然数
                                ( 後者を計算する_自然数 m_p )
                                ( 後者を計算する_自然数 ( 後者を計算する_自然数 n_p ) )
                        )
                        (
                            後者を計算する_自然数
                                ( 足す_自然数 ( 後者を計算する_自然数 m_p ) ( 後者を計算する_自然数 n_p ) )
                        )
                )
            .
            change
                (
                    道@{ i }
                        自然数@{ i }
                        (
                            後者を計算する_自然数
                                ( 後者を計算する_自然数 ( 足す_自然数 m_p ( 後者を計算する_自然数 n_p ) ) )
                        )
                        (
                            後者を計算する_自然数
                                ( 後者を計算する_自然数 ( 後者を計算する_自然数 ( 足す_自然数 m_p n_p ) ) )
                        )
                )
            .
            refine
                (
                    関数を適用する_道
                        自然数@{ i }
                        自然数@{ i }
                        ( fun x : 自然数@{ i } => 後者を計算する_自然数 ( 後者を計算する_自然数 x ) )
                        ( 足す_自然数 m_p ( 後者を計算する_自然数 n_p ) )
                        ( 後者を計算する_自然数 ( 足す_自然数 m_p n_p ) )
                        _
                )
            .
            exact ( a m_p n_p ).
Defined.

Definition A_2024_01_25_0003@{ i | } ( m : 自然数@{ i } ) ( n : 自然数@{ i } )
    : 道@{ i } 自然数@{ i } ( 足す_自然数 ( 後者を計算する_自然数 m ) n ) ( 後者を計算する_自然数 ( 足す_自然数 m n ) )
.
Proof.
    refine ( let a := _ in a m n ).
    refine
        (
            fix a ( m : 自然数@{ i } ) ( n : 自然数@{ i } ) { struct m }
                :
                    道@{ i }
                        自然数@{ i }
                        ( 足す_自然数 ( 後者を計算する_自然数 m ) n )
                        ( 後者を計算する_自然数 ( 足す_自然数 m n ) )
                := _
        )
    .
    refine
        (
            match
                m
            as
                m_
            return
                道@{ i }
                    自然数@{ i }
                    ( 足す_自然数 ( 後者を計算する_自然数 m_ ) n )
                    ( 後者を計算する_自然数 ( 足す_自然数 m_ n ) )
            with
                零_構築子_自然数 => _
                |
                後者_構築子_自然数 m_p => _
            end
        )
    .
    -
        refine
            (
                match
                    n
                as
                    n_
                return
                    道@{ i }
                        自然数@{ i }
                        ( 足す_自然数 ( 後者を計算する_自然数 零_自然数 ) n_ )
                        ( 後者を計算する_自然数 ( 足す_自然数 零_自然数 n_ ) )
                with
                    零_構築子_自然数 => _
                    |
                    後者_構築子_自然数 n_p => _
                end
            )
        .
        +
            change
                (
                    道@{ i }
                        自然数@{ i }
                        ( 足す_自然数 ( 後者を計算する_自然数 零_自然数 ) 零_自然数 )
                        ( 後者を計算する_自然数 ( 足す_自然数 零_自然数 零_自然数 ) )
                )
            .
            change ( 道@{ i } 自然数@{ i } ( 後者を計算する_自然数 零_自然数 ) ( 後者を計算する_自然数 零_自然数 ) ).
            exact ( 恒等道_道 自然数@{ i } ( 後者を計算する_自然数 零_自然数 ) ).
        +
            change
                (
                    道@{ i }
                        自然数@{ i }
                        ( 足す_自然数 ( 後者を計算する_自然数 零_自然数 ) ( 後者を計算する_自然数 n_p ) )
                        ( 後者を計算する_自然数 ( 足す_自然数 零_自然数 ( 後者を計算する_自然数 n_p ) ) )
                )
            .
            change
                (
                    道@{ i }
                        自然数@{ i }
                        ( 後者を計算する_自然数 ( 後者を計算する_自然数 ( 足す_自然数 零_自然数 n_p ) ) )
                        ( 後者を計算する_自然数 ( 後者を計算する_自然数 n_p ) )
                )
            .
            refine
                (
                    関数を適用する_道
                        自然数@{ i }
                        自然数@{ i }
                        ( fun x : 自然数@{ i } => 後者を計算する_自然数 ( 後者を計算する_自然数 x ) )
                        ( 足す_自然数 零_自然数 n_p )
                        n_p
                        _
                )
            .
            exact ( A_2024_01_25_0001 n_p ).
    -
        refine
            (
                match
                    n
                as
                    n_
                return
                    道@{ i }
                        自然数@{ i }
                        ( 足す_自然数 ( 後者を計算する_自然数 ( 後者を計算する_自然数 m_p ) ) n_ )
                        ( 後者を計算する_自然数 ( 足す_自然数 ( 後者を計算する_自然数 m_p ) n_ ) )
                with
                    零_構築子_自然数 => _
                    |
                    後者_構築子_自然数 n_p => _
                end
            )
        .
        +
            change
                (
                    道@{ i }
                        自然数@{ i }
                        ( 足す_自然数 ( 後者を計算する_自然数 ( 後者を計算する_自然数 m_p ) ) 零_自然数 )
                        ( 後者を計算する_自然数 ( 足す_自然数 ( 後者を計算する_自然数 m_p ) 零_自然数 ) )
                )
            .
            change
                (
                    道@{ i }
                        自然数@{ i }
                        ( 後者を計算する_自然数 ( 後者を計算する_自然数 m_p ) )
                        ( 後者を計算する_自然数 ( 後者を計算する_自然数 m_p ) )
                )
            .
            exact ( 恒等道_道 自然数@{ i } ( 後者を計算する_自然数 ( 後者を計算する_自然数 m_p ) ) ).
        +
            change
                (
                    道@{ i }
                        自然数@{ i }
                        (
                            足す_自然数
                                ( 後者を計算する_自然数 ( 後者を計算する_自然数 m_p ) )
                                ( 後者を計算する_自然数 n_p )
                        )
                        (
                            後者を計算する_自然数
                                ( 足す_自然数 ( 後者を計算する_自然数 m_p ) ( 後者を計算する_自然数 n_p ) )
                        )
                )
            .
            change
                (
                    道@{ i }
                        自然数@{ i }
                        (
                            後者を計算する_自然数
                                ( 後者を計算する_自然数 ( 足す_自然数 ( 後者を計算する_自然数 m_p ) n_p ) )
                        )
                        (
                            後者を計算する_自然数
                                ( 後者を計算する_自然数 ( 後者を計算する_自然数 ( 足す_自然数 m_p n_p ) ) )
                        )
                )
            .
            refine
                (
                    関数を適用する_道
                        自然数@{ i }
                        自然数@{ i }
                        ( fun x : 自然数@{ i } => 後者を計算する_自然数 ( 後者を計算する_自然数 x ) )
                        ( 足す_自然数 ( 後者を計算する_自然数 m_p ) n_p )
                        ( 後者を計算する_自然数 ( 足す_自然数 m_p n_p ) )
                        _
                )
            .
            exact ( a m_p n_p ).
Defined.
