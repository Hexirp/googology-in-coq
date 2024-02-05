(** Playground モジュールは、まだ単独のモジュールに分割していないコードを置く場所です。 *)

Require Googology_In_Coq.Base.

Import Googology_In_Coq.Base.

(** 関数型を定義します。 *)

Definition 関数@{ i | } ( A : Type@{ i } ) ( B : Type@{ i } ) : Type@{ i } := A -> B.

Definition 恒等関数_関数@{ i | } ( A : Type@{ i } ) : A -> A := fun x : A => x.

Definition 合成する_関数@{ i | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( C : Type@{ i } ) ( f : B -> C ) ( g : A -> B )
    : A -> C
    := fun x : A => f ( g x )
.

Definition 定数関数_関数@{ i } ( A : Type@{ i } ) ( B : Type@{ i } ) ( x : A ) : B -> A := fun y : B => x.

(** 空型を定義します。「空型」は "empty type" の訳語です。 *)

Inductive 空型@{ i | } : Type@{ i } :=.

(** 「不条理である」は "absurd" の訳語です。 *)

Definition 不条理である_空型@{ i | } ( A : Type@{ i } ) ( x : 空型@{ i } ) : A := match x with end.

(** 否定を定義します。 *)

Definition 否定@{ i | } ( A : Type@{ i } ) : Type@{ i } := A -> 空型@{ i }.

Definition A_2024_01_26_0000@{ i | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( f : A -> B ) : 否定@{ i } B -> 否定@{ i } A
    := fun x : 否定@{ i } B => fun y : A => x ( f y )
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

(** 単一型を定義します。「単一型」は "unit type" の訳語です。 *)

Inductive 単一型@{ i | } : Type@{ i } := 構築子_単一型 : 単一型.

(** 直積型を定義します。 *)

Inductive 直積@{ i | } ( A : Type@{ i } ) ( B : Type@{ i } ) : Type@{ i } := 構築子_直積 : A -> B -> 直積 A B.


Definition 構築する_直積@{ i | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( x : A ) ( y : B ) : 直積@{ i } A B
    := 構築子_直積 A B x y
.

Definition 第一射影関数_直積@{ i | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( x : 直積@{ i } A B ) : A
    := match x with 構築子_直積 _ _ x_1 x_2 => x_1 end
.

Definition 第二射影関数_直積@{ i | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( x : 直積@{ i } A B ) : B
    := match x with 構築子_直積 _ _ x_1 x_2 => x_2 end
.

Definition カリー化する_直積@{ i | }
        ( A : Type@{ i } )
        ( B : Type@{ i } )
        ( C : Type@{ i } )
        ( f : 直積@{ i } A B -> C )
    : A -> B -> C
    := fun ( x_1 : A ) ( x_2 : B ) => f ( 構築する_直積 A B x_1 x_2 )
.

Definition 非カリー化する_直積@{ i | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( C : Type@{ i } ) ( f : A -> B -> C )
    : 直積@{ i } A B -> C
    := fun x : 直積@{ i } A B => match x with 構築子_直積 _ _ x_1 x_2 => f x_1 x_2 end
.

(** 依存直和型を定義します。 *)

Inductive 依存直和@{ i | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) : Type@{ i }
    := 構築子_依存直和 : forall x : A, B x -> 依存直和 A B
.

Definition 構築する_依存直和@{ i | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( x : A ) ( y : B x )
    : 依存直和@{ i } A B
    := 構築子_依存直和 A B x y
.

Definition 第一射影関数_依存直和@{ i | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( x : 依存直和@{ i } A B ) : A
    := match x with 構築子_依存直和 _ _ x_1 x_2 => x_1 end
.

Definition 第二射影関数_依存直和@{ i | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( x : 依存直和@{ i } A B )
    : B ( 第一射影関数_依存直和 A B x )
    := match x as x_ return B ( 第一射影関数_依存直和 A B x_ ) with 構築子_依存直和 _ _ x_1 x_2 => x_2 end
.

Definition カリー化する_依存直和@{ i | }
        ( A : Type@{ i } )
        ( B : A -> Type@{ i } )
        ( C : Type@{ i } )
        ( f : 依存直和@{ i } A B -> C )
    : forall x : A, B x -> C
    := fun ( x_1 : A ) ( x_2 : B x_1 ) => f ( 構築する_依存直和 A B x_1 x_2 )
.

Definition 非カリー化する_依存直和@{ i | }
        ( A : Type@{ i } )
        ( B : A -> Type@{ i } )
        ( C : Type@{ i } )
        ( f : forall x : A, B x -> C )
    : 依存直和@{ i } A B -> C
    := fun x : 依存直和@{ i } A B => match x with 構築子_依存直和 _ _ x_1 x_2 => f x_1 x_2 end
.

(** 依存直積型を定義します。 *)

Definition 依存直積@{ i | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) : Type@{ i } := forall x : A, B x.

(** ブール型を定義します。「ブール型」は "boolean type" の訳語です。 *)

Inductive ブール型@{ i | } : Type@{ i } := 偽_構築子_ブール型 : ブール型 | 真_構築子_ブール型 : ブール型.

(** 自然数を定義します。 *)

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

Definition 一を足す_自然数@{ i | } : 自然数@{ i } -> 自然数@{ i } := 後者を計算する_自然数.

Definition 二を足す_自然数@{ i | } ( x : 自然数@{ i } ) : 自然数@{ i } := 後者を計算する_自然数 ( 一を足す_自然数 x ).

Definition 三を足す_自然数@{ i | } ( x : 自然数@{ i } ) : 自然数@{ i } := 後者を計算する_自然数 ( 二を足す_自然数 x ).

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

(** 道を定義します。「道」は "path" の訳語です。 *)

Inductive 道@{ i | } ( A : Type@{ i } ) ( x : A ) : A -> Type@{ i } := 構築子_道 : 道 A x x.

(** 「恒等道」は "identity path" の訳語です。 *)

Definition 恒等道_道@{ i | } ( A : Type@{ i } ) ( x : A ) : 道 A x x := 構築子_道 A x.

Definition 結合する_道@{ i | } ( A : Type@{ i } ) ( x : A ) ( y : A ) ( z : A ) ( p : 道 A x y ) ( q : 道 A y z )
    : 道 A x z
    :=
        match
            q
        in
            道 _ _ z_
        return
            道 A x z_
        with
            構築子_道 _ _ => match p in 道 _ _ y_ return 道 A x y_ with 構築子_道 _ _ => 恒等道_道 A x end
        end
.

Definition 反転する_道@{ i | } ( A : Type@{ i } ) ( x : A ) ( y : A ) ( p : 道 A x y ) : 道 A y x
    := match p in 道 _ _ y_ return 道 A y_ x with 構築子_道 _ _ => 構築子_道 A x end
.

Definition 関数を適用する_道@{ i | }
        ( A : Type@{ i } )
        ( B : Type@{ i } )
        ( f : A -> B )
        ( x : A )
        ( y : A )
        ( p : 道 A x y )
    : 道 B ( f x ) ( f y )
    := match p in 道 _ _ y_ return 道@{ i } B ( f x ) ( f y_ ) with 構築子_道 _ _ => 構築子_道 B ( f x ) end
.

(** 「輸送する」は "transport" の訳語です。 *)

Definition 輸送する_道@{ i | }
        ( A : Type@{ i } )
        ( B : A -> Type@{ i } )
        ( x : A )
        ( y : A )
        ( p : 道@{ i } A x y )
        ( u : B x )
    : B y
    := match p in 道 _ _ y_ return B y_ with 構築子_道 _ _ => u end
.

Definition 依存関数を適用する_道@{ i | }
        ( A : Type@{ i } )
        ( B : A -> Type@{ i } )
        ( f : forall x : A, B x )
        ( x : A )
        ( y : A )
        ( p : 道@{ i } A x y )
    : 道@{ i } ( B y ) ( 輸送する_道 A B x y p ( f x ) ) ( f y )
    :=
        match
            p
        as
            p_
        in
            道 _ _ y_
        return
            道@{ i } ( B y_ ) ( 輸送する_道 A B x y_ p_ ( f x ) ) ( f y_ )
        with
            構築子_道 _ _ => 恒等道_道 ( B x ) ( f x )
        end
.

(** 道の定理を証明します。 *)

Definition A_2024_02_01_0000@{ i | } ( A : Type@{ i } ) ( x : A )
    : 道@{ i } ( 道@{ i } A x x ) ( 結合する_道 A x x x ( 恒等道_道 A x ) ( 恒等道_道 A x ) ) ( 恒等道_道 A x )
    := 恒等道_道 _ _
.

Definition A_2024_02_06_0005@{ i | } ( A : Type@{ i } ) ( x : A )
    : 道@{ i } ( 道@{ i } A x x ) ( 反転する_道 A x x ( 恒等道_道 A x ) ) ( 恒等道_道 A x )
    := 恒等道_道 _ _
.

Definition A_2024_02_06_0008@{ i | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( f : A -> B ) ( x : A )
    : 道@{ i } ( 道@{ i } A x x ) ( 関数を適用する A B f x x ( 恒等道_道 A x ) ) ( 恒等道_道 B ( f x ) )
    := 恒等道_道 _ _
.

Definition A_2024_02_06_0006@{ i | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( x : A ) ( u : B x )
    : 道@{ i } ( B x ) ( 輸送する_道 A B x x ( 恒等道_道 A x ) u ) u
    := 恒等道_道 _ _
.

Definition A_2024_02_06_0007@{ i | } ( A : Type@{ i } ) ( B : A -> Type@{ i } ) ( f : forall x : A, B x ) ( x : A )
    :
        道@{ i }
            ( 道@{ i } ( B x ) ( f x ) ( f x ) )
            ( 依存関数を適用する_道 A B f x x ( 恒等道_道 A x ) )
            ( 恒等道_道 ( B x ) ( f x ) )
    := 恒等道_道 _ _
.

Definition 結合演算の結合法則_道@{ i | }
        ( A : Type@{ i } )
        ( x : A )
        ( y : A )
        ( z : A )
        ( w : A )
        ( p : 道@{ i } A x y )
        ( q : 道@{ i } A y z )
        ( r : 道@{ i } A z w )
    :
        道@{ i }
            ( 道@{ i } A x w )
            ( 結合する_道 A x z w ( 結合する_道 A x y z p q ) r )
            ( 結合する_道 A x y w p ( 結合する_道 A y z w q r ) )
.
Proof.
    refine
        (
            match
                r
            as
                r_
            in
                道 _ _ w_
            return
                道@{ i }
                    ( 道@{ i } A x w_ )
                    ( 結合する_道 A x z w_ ( 結合する_道 A x y z p q ) r_ )
                    ( 結合する_道 A x y w_ p ( 結合する_道 A y z w_ q r_ ) )
            with
                構築子_道 _ _ => _
            end
        )
    .
    refine
        (
            match
                q
            as
                q_
            in
                道 _ _ z_
            return
                道@{ i }
                    ( 道@{ i } A x z_ )
                    ( 結合する_道 A x z_ z_ ( 結合する_道 A x y z_ p q_ ) ( 恒等道_道 A z_ ) )
                    ( 結合する_道 A x y z_ p ( 結合する_道 A y z_ z_ q_ ( 恒等道_道 A z_ ) ) )
            with
                構築子_道 _ _ => _
            end
        )
    .
    refine
        (
            match
                p
            as
                p_
            in
                道 _ _ y_
            return
                道@{ i }
                    ( 道@{ i } A x y_ )
                    ( 結合する_道 A x y_ y_ ( 結合する_道 A x y_ y_ p_ ( 恒等道_道 A y_ ) ) ( 恒等道_道 A y_ ) )
                    ( 結合する_道 A x y_ y_ p_ ( 結合する_道 A y_ y_ y_ ( 恒等道_道 A y_ ) ( 恒等道_道 A y_ ) ) )
            with
                構築子_道 _ _ => _
            end
        )
    .
    change
        (
            道@{ i }
                ( 道@{ i } A x x )
                ( 結合する_道 A x x x ( 結合する_道 A x x x ( 恒等道_道 A x ) ( 恒等道_道 A x ) ) ( 恒等道_道 A x ) )
                ( 結合する_道 A x x x ( 恒等道_道 A x ) ( 結合する_道 A x x x ( 恒等道_道 A x ) ( 恒等道_道 A x ) ) )
        )
    .
    change ( 道@{ i } ( 道@{ i } A x x ) ( 恒等道_道 A x ) ( 恒等道_道 A x ) ).
    exact ( 恒等道_道 ( 道@{ i } A x x ) ( 恒等道_道 A x ) ).
Defined.

Definition A_2024_02_01_0001@{ i | } ( A : Type@{ i } ) ( x : A ) ( y : A ) ( p : 道@{ i } A x y )
    : 道@{ i } ( 道@{ i } A x y ) ( 結合する_道 A x y y p ( 恒等道_道 A y ) ) p
    :=
        match
            p
        as
            p_
        in
            道 _ _ y_
        return
            道@{ i } ( 道@{ i } A x y_ ) ( 結合する_道 A x y_ y_ p_ ( 恒等道_道 A y_ ) ) p_
        with
            構築子_道 _ _ => 恒等道_道 ( 道@{ i } A x x ) ( 恒等道_道 A x )
        end
.

Definition A_2024_02_01_0002@{ i | } ( A : Type@{ i } ) ( x : A ) ( y : A ) ( p : 道@{ i } A x y )
    : 道@{ i } ( 道@{ i } A x y ) ( 結合する_道 A x x y ( 恒等道_道 A x ) p ) p
    :=
        match
            p
        as
            p_
        in
            道 _ _ y_
        return
            道@{ i } ( 道@{ i } A x y_ ) ( 結合する_道 A x x y_ ( 恒等道_道 A x ) p_ ) p_
        with
            構築子_道 _ _ => 恒等道_道 ( 道@{ i } A x x ) ( 恒等道_道 A x )
        end
.

Definition A_2024_02_05_0000@{ i | } ( A : Type@{ i } ) ( x : A ) ( y : A ) ( p : 道@{ i } A x y )
    : 道@{ i } ( 道@{ i } A y y ) ( 結合する_道 A y x y ( 反転する_道 A x y p ) p ) ( 恒等道_道 A y )
    :=
        match
            p
        as
            p_
        in
            道 _ _ y_
        return
            道@{ i } ( 道@{ i } A y_ y_ ) ( 結合する_道 A y_ x y_ ( 反転する_道 A x y_ p_ ) p_ ) ( 恒等道_道 A y_ )
        with
            構築子_道 _ _ => 恒等道_道 ( 道@{ i } A x x ) ( 恒等道_道 A x )
        end
.

Definition A_2024_02_05_0001@{ i | } ( A : Type@{ i } ) ( x : A ) ( y : A ) ( p : 道@{ i } A x y )
    : 道@{ i } ( 道@{ i } A x x ) ( 結合する_道 A x y x p ( 反転する_道 A x y p ) ) ( 恒等道_道 A x )
    :=
        match
            p
        as
            p_
        in
            道 _ _ y_
        return
            道@{ i } ( 道@{ i } A x x ) ( 結合する_道 A x y_ x p_ ( 反転する_道 A x y_ p_ ) ) ( 恒等道_道 A x )
        with
            構築子_道 _ _ => 恒等道_道 ( 道@{ i } A x x ) ( 恒等道_道 A x )
        end
.

Definition A_2024_02_06_0000@{ i | } ( A : Type@{ i } ) ( x : A ) ( y : A ) ( p : 道@{ i } A x y )
    : 道@{ i } ( 道@{ i } A x y ) ( 関数を適用する_道 A A ( 恒等関数_関数 A ) x y p ) p
    :=
        match
            p
        as
            p_
        in
            道 _ _ y_
        return
            道@{ i } ( 道@{ i } A x y_ ) ( 関数を適用する_道 A A ( 恒等関数_関数 A ) x y_ p_ ) p_
        with
            構築子_道 _ _ => 恒等道_道 ( 道@{ i } A x x ) ( 恒等道_道 A x )
        end
.

Definition A_2024_02_06_0001@{ i | }
        ( A : Type@{ i } )
        ( B : Type@{ i } )
        ( C : Type@{ i } )
        ( f : B -> C )
        ( g : A -> B )
        ( x : A )
        ( y : A )
        ( p : 道@{ i } A x y )
    :
        道@{ i }
            ( 道@{ i } C ( f ( g x ) ) ( f ( g y ) ) )
            ( 関数を適用する_道 A C ( 合成する_関数 A B C f g ) x y p )
            ( 関数を適用する_道 B C f ( g x ) ( g y ) ( 関数を適用する_道 A B g x y p ) )
    :=
        match
            p
        as
            p_
        in
            道 _ _ y_
        return
            道@{ i }
                ( 道@{ i } C ( f ( g x ) ) ( f ( g y_ ) ) )
                ( 関数を適用する_道 A C ( 合成する_関数 A B C f g ) x y_ p_ )
                ( 関数を適用する_道 B C f ( g x ) ( g y_ ) ( 関数を適用する_道 A B g x y_ p_ ) )
        with
            構築子_道 _ _ => 恒等道_道 ( 道@{ i } C ( f ( g x ) ) ( f ( g x ) ) ) ( 恒等道_道 C ( f ( g x ) ) )
        end
.

Definition A_2024_02_06_0002@{ i | } ( A : Type@{ i } ) ( B : Type@{ i } ) ( f : A -> B ) ( x : A )
    : 道@{ i } ( 道@{ i } B ( f x ) ( f x ) ) ( 関数を適用する_道 A B f x x ( 恒等道_道 A x ) ) ( 恒等道_道 B ( f x ) )
    := 恒等道_道 ( 道@{ i } B ( f x ) ( f x ) ) ( 恒等道_道 B ( f x ) )
.

Definition A_2024_02_06_0003@{ i | }
        ( A : Type@{ i } )
        ( B : Type@{ i } )
        ( f : A -> B )
        ( x : A )
        ( y : A )
        ( z : A )
        ( p : 道@{ i } A x y )
        ( q : 道@{ i } A y z )
    :
        道@{ i }
            ( 道@{ i } B ( f x ) ( f z ) )
            ( 関数を適用する_道 A B f x z ( 結合する_道 A x y z p q ) )
            ( 結合する_道 B ( f x ) ( f y ) ( f z ) ( 関数を適用する_道 A B f x y p ) ( 関数を適用する_道 A B f y z q ) )
.
Proof.
    refine
        (
            match
                q
            as
                q_
            in
                道 _ _ z_
            return
                道@{ i }
                    ( 道@{ i } B ( f x ) ( f z_ ) )
                    ( 関数を適用する_道 A B f x z_ ( 結合する_道 A x y z_ p q_ ) )
                    (
                        結合する_道
                            B
                            ( f x )
                            ( f y )
                            ( f z_ )
                            ( 関数を適用する_道 A B f x y p )
                            ( 関数を適用する_道 A B f y z_ q_ )
                    )
            with
                構築子_道 _ _ => _
            end
        )
    .
    refine
        (
            match
                p
            as
                p_
            in
                道 _ _ y_
            return
                道@{ i }
                    ( 道@{ i } B ( f x ) ( f y_ ) )
                    ( 関数を適用する_道 A B f x y_ ( 結合する_道 A x y_ y_ p_ ( 恒等道_道 A y_ ) ) )
                    (
                        結合する_道
                            B
                            ( f x )
                            ( f y_ )
                            ( f y_ )
                            ( 関数を適用する_道 A B f x y_ p_ )
                            ( 関数を適用する_道 A B f y_ y_ ( 恒等道_道 A y_ ) )
                    )
            with
                構築子_道 _ _ => _
            end
        )
    .
    change
        (
            道@{ i }
                ( 道@{ i } B ( f x ) ( f x ) )
                ( 関数を適用する_道 A B f x x ( 結合する_道 A x x x ( 恒等道_道 A x ) ( 恒等道_道 A x ) ) )
                (
                    結合する_道
                        B
                        ( f x )
                        ( f x )
                        ( f x )
                        ( 関数を適用する_道 A B f x x ( 恒等道_道 A x ) )
                        ( 関数を適用する_道 A B f x x ( 恒等道_道 A x ) )
                )
        )
    .
    change ( 道@{ i } ( 道@{ i } B ( f x ) ( f x ) ) ( 恒等道_道 B ( f x ) ) ( 恒等道_道 B ( f x ) ) ).
    exact ( 恒等道_道 ( 道@{ i } B ( f x ) ( f x ) ) ( 恒等道_道 B ( f x ) ) ).
Defined.

Definition A_2024_02_06_0004@{ i | }
        ( A : Type@{ i } )
        ( B : Type@{ i } )
        ( f : A -> B )
        ( x : A )
        ( y : A )
        ( p : 道@{ i } A x y )
    :
        道@{ i }
            ( 道@{ i } B ( f y ) ( f x ) )
            ( 関数を適用する_道 A B f y x ( 反転する_道 A x y p ) )
            ( 反転する_道 B ( f x ) ( f y ) ( 関数を適用する_道 A B f x y p ) )
    :=
        match
            p
        as
            p_
        in
            道 _ _ y_
        return
            道@{ i }
                ( 道@{ i } B ( f y_ ) ( f x ) )
                ( 関数を適用する_道 A B f y_ x ( 反転する_道 A x y_ p_ ) )
                ( 反転する_道 B ( f x ) ( f y_ ) ( 関数を適用する_道 A B f x y_ p_ ) )
        with
            構築子_道 _ _ => 恒等道_道 ( 道@{ i } B ( f x ) ( f x ) ) ( 恒等道_道 B ( f x ) )
        end
.

(** 基点付き道を定義します。 *)

Definition 基点付き道@{ i | } ( A : Type@{ i } ) ( x : A ) : Type@{ i }
    := 依存直和@{ i } A ( fun y : A => 道@{ i } A x y )
.

Definition 基点付き恒等道_基点付き道@{ i | } ( A : Type@{ i } ) ( x : A ) : 基点付き道@{ i } A x
    := 構築する_依存直和 A ( fun y : A => 道@{ i } A x y ) x ( 恒等道_道 A x )
.

Definition A_2024_01_30_0000@{ i | } ( A : Type@{ i } ) ( x : A ) ( p : 基点付き道@{ i } A x )
    : 道@{ i } ( 基点付き道@{ i } A x ) ( 基点付き恒等道_基点付き道 A x ) p
.
Proof.
    refine
        (
            match
                p
            as
                p_
            return
                道@{ i } ( 基点付き道@{ i } A x ) ( 基点付き恒等道_基点付き道 A x ) p_
            with
                構築子_依存直和 _ _ y p => _
            end
        )
    .
    refine
        (
            match
                p
            as
                p_
            in
                道 _ _ y_
            return
                道@{ i }
                    ( 基点付き道@{ i } A x )
                    ( 基点付き恒等道_基点付き道 A x )
                    ( 構築する_依存直和 A ( fun y : A => 道@{ i } A x y ) y_ p_ )
            with
                構築子_道 _ _ => _
            end
        )
    .
    change
        (
            道@{ i }
                ( 基点付き道@{ i } A x )
                ( 基点付き恒等道_基点付き道 A x )
                ( 構築する_依存直和 A ( fun y : A => 道@{ i } A x y ) x ( 恒等道_道 A x ) )
        )
    .
    change ( 道@{ i } ( 基点付き道@{ i } A x ) ( 基点付き恒等道_基点付き道 A x ) ( 基点付き恒等道_基点付き道 A x ) ).
    exact ( 恒等道_道 ( 基点付き道@{ i } A x ) ( 基点付き恒等道_基点付き道 A x ) ).
Defined.

(** 自然数の定理を証明します。 *)

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

Definition A_2024_01_29_0000@{ i | } : 道@{ i } 自然数@{ i } ( 足す_自然数 零_自然数 零_自然数 ) 零_自然数
    := 恒等道_道 _ _
.

Definition A_2024_01_29_0001@{ i | } ( m : 自然数@{ i } )
    : 道@{ i } 自然数@{ i } ( 足す_自然数 ( 後者を計算する_自然数 m ) 零_自然数 ) ( 後者を計算する_自然数 m )
    := 恒等道_道 _ _
.

Definition A_2024_01_29_0002@{ i | } ( n : 自然数@{ i } )
    : 道@{ i } 自然数@{ i } ( 足す_自然数 零_自然数 ( 後者を計算する_自然数 n ) ) ( 後者を計算する_自然数 n )
    := 恒等道_道 _ _
.

Definition A_2024_01_29_0003@{ i | } ( m : 自然数@{ i } ) ( n : 自然数@{ i } )
    :
        道@{ i }
            自然数@{ i }
            ( 足す_自然数 ( 後者を計算する_自然数 m ) ( 後者を計算する_自然数 n ) )
            ( 後者を計算する_自然数 ( 後者を計算する_自然数 ( 足す_自然数 m n ) ) )
    := 恒等道_道 _ _
.

Definition A_2024_01_25_0000@{ i | } ( m : 自然数@{ i } ) : 道@{ i } 自然数@{ i } ( 足す_自然数 m 零_自然数 ) m
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

Definition A_2024_01_25_0001@{ i | } ( n : 自然数@{ i } ) : 道@{ i } 自然数@{ i } ( 足す_自然数 零_自然数 n ) n
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
                零_構築子_自然数 => _ | 後者_構築子_自然数 m_p => _
            end
        )
    .
    {
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
                    零_構築子_自然数 => _ | 後者_構築子_自然数 n_p => _
                end
            )
        .
        {
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
        }
        {
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
        }
    }
    {
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
                    零_構築子_自然数 => _ | 後者_構築子_自然数 n_p => _
                end
            )
        .
        {
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
            change ( 道@{ i } 自然数@{ i } ( 二を足す_自然数 ( 足す_自然数 m_p 零_自然数 ) ) ( 二を足す_自然数 m_p ) ).
            refine ( 関数を適用する_道 自然数@{ i } 自然数@{ i } 二を足す_自然数 ( 足す_自然数 m_p 零_自然数 ) m_p _ ).
            exact ( A_2024_01_25_0000 m_p ).
        }
        {
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
            change
                (
                    道@{ i }
                        自然数@{ i }
                        ( 二を足す_自然数 ( 足す_自然数 m_p ( 後者を計算する_自然数 n_p ) ) )
                        ( 二を足す_自然数 ( 後者を計算する_自然数 ( 足す_自然数 m_p n_p ) ) )
                )
            .
            refine
                (
                    関数を適用する_道
                        自然数@{ i }
                        自然数@{ i }
                        二を足す_自然数
                        ( 足す_自然数 m_p ( 後者を計算する_自然数 n_p ) )
                        ( 後者を計算する_自然数 ( 足す_自然数 m_p n_p ) )
                        _
                )
            .
            exact ( a m_p n_p ).
        }
    }
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
                零_構築子_自然数 => _ | 後者_構築子_自然数 m_p => _
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
                    零_構築子_自然数 => _ | 後者_構築子_自然数 n_p => _
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
            change ( 道@{ i } 自然数@{ i } ( 二を足す_自然数 ( 足す_自然数 零_自然数 n_p ) ) ( 二を足す_自然数 n_p ) ).
            refine ( 関数を適用する_道 自然数@{ i } 自然数@{ i } 二を足す_自然数 ( 足す_自然数 零_自然数 n_p ) n_p _ ).
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
                    零_構築子_自然数 => _ | 後者_構築子_自然数 n_p => _
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
            change
                (
                    道@{ i }
                        自然数@{ i }
                        ( 二を足す_自然数 ( 足す_自然数 ( 後者を計算する_自然数 m_p ) n_p ) )
                        ( 二を足す_自然数 ( 後者を計算する_自然数 ( 足す_自然数 m_p n_p ) ) )
                )
            .
            refine
                (
                    関数を適用する_道
                        自然数@{ i }
                        自然数@{ i }
                        二を足す_自然数
                        ( 足す_自然数 ( 後者を計算する_自然数 m_p ) n_p )
                        ( 後者を計算する_自然数 ( 足す_自然数 m_p n_p ) )
                        _
                )
            .
            exact ( a m_p n_p ).
Defined.

Definition 加算の結合法則_自然数@{ i | } ( m : 自然数@{ i } ) ( n : 自然数@{ i } ) ( o : 自然数@{ i } )
    : 道@{ i } 自然数@{ i } ( 足す_自然数 ( 足す_自然数 m n ) o ) ( 足す_自然数 m ( 足す_自然数 n o ) )
.
Proof.
    refine ( let a := _ in a m n o ).
    refine
        (
            fix a ( m : 自然数@{ i } ) ( n : 自然数@{ i } ) ( o : 自然数@{ i } ) { struct m }
                : 道@{ i } 自然数@{ i } ( 足す_自然数 ( 足す_自然数 m n ) o ) ( 足す_自然数 m ( 足す_自然数 n o ) )
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
                道@{ i } 自然数@{ i } ( 足す_自然数 ( 足す_自然数 m_ n ) o ) ( 足す_自然数 m_ ( 足す_自然数 n o ) )
            with
                零_構築子_自然数 => _ | 後者_構築子_自然数 m_p => _
            end
        )
    .
    {
        refine
            (
                match
                    n
                as
                    n_
                return
                    道@{ i }
                        自然数@{ i }
                        ( 足す_自然数 ( 足す_自然数 零_自然数 n_ ) o )
                        ( 足す_自然数 零_自然数 ( 足す_自然数 n_ o ) )
                with
                    零_構築子_自然数 => _ | 後者_構築子_自然数 n_p => _
                end
            )
        .
        {
            refine
                (
                    match
                        o
                    as
                        o_
                    return
                        道@{ i }
                            自然数@{ i }
                            ( 足す_自然数 ( 足す_自然数 零_自然数 零_自然数 ) o_ )
                            ( 足す_自然数 零_自然数 ( 足す_自然数 零_自然数 o_ ) )
                    with
                        零_構築子_自然数 => _ | 後者_構築子_自然数 o_p => _
                    end
                )
            .
            {
                change
                    (
                        道@{ i }
                            自然数@{ i }
                            ( 足す_自然数 ( 足す_自然数 零_自然数 零_自然数 ) 零_自然数 )
                            ( 足す_自然数 零_自然数 ( 足す_自然数 零_自然数 零_自然数 ) )
                    )
                .
                change ( 道@{ i } 自然数@{ i } 零_自然数 零_自然数 ).
                exact ( 恒等道_道 自然数@{ i } 零_自然数 ).
            }
            {
                change
                    (
                        道@{ i }
                            自然数@{ i }
                            ( 足す_自然数 ( 足す_自然数 零_自然数 零_自然数 ) ( 後者を計算する_自然数 o_p ) )
                            ( 足す_自然数 零_自然数 ( 足す_自然数 零_自然数 ( 後者を計算する_自然数 o_p ) ) )
                    )
                .
                change ( 道@{ i } 自然数@{ i } ( 後者を計算する_自然数 o_p ) ( 後者を計算する_自然数 o_p ) ).
                exact ( 恒等道_道 自然数@{ i } ( 後者を計算する_自然数 o_p ) ).
            }
        }
        {
            refine
                (
                    match
                        o
                    as
                        o_
                    return
                        道@{ i }
                            自然数@{ i }
                            ( 足す_自然数 ( 足す_自然数 零_自然数 ( 後者を計算する_自然数 n_p ) ) o_ )
                            ( 足す_自然数 零_自然数 ( 足す_自然数 ( 後者を計算する_自然数 n_p ) o_ ) )
                    with
                        零_構築子_自然数 => _ | 後者_構築子_自然数 o_p => _
                    end
                )
            .
            {
                change
                    (
                        道@{ i }
                            自然数@{ i }
                            ( 足す_自然数 ( 足す_自然数 零_自然数 ( 後者を計算する_自然数 n_p ) ) 零_自然数 )
                            ( 足す_自然数 零_自然数 ( 足す_自然数 ( 後者を計算する_自然数 n_p ) 零_自然数 ) )
                    )
                .
                change ( 道@{ i } 自然数@{ i } ( 後者を計算する_自然数 n_p ) ( 後者を計算する_自然数 n_p ) ).
                exact ( 恒等道_道 自然数@{ i } ( 後者を計算する_自然数 n_p ) ).
            }
            {
                change
                    (
                        道@{ i }
                            自然数@{ i }
                            (
                                足す_自然数
                                    ( 足す_自然数 零_自然数 ( 後者を計算する_自然数 n_p ) )
                                    ( 後者を計算する_自然数 o_p )
                            )
                            (
                                足す_自然数
                                    零_自然数
                                    ( 足す_自然数 ( 後者を計算する_自然数 n_p ) ( 後者を計算する_自然数 o_p ) )
                            )
                    )
                .
                change
                    (
                        道@{ i }
                            自然数@{ i }
                            ( 後者を計算する_自然数 ( 後者を計算する_自然数 ( 足す_自然数 n_p o_p ) ) )
                            ( 後者を計算する_自然数 ( 後者を計算する_自然数 ( 足す_自然数 n_p o_p ) ) )
                    )
                .
                exact
                    (
                        恒等道_道
                            自然数@{ i }
                            ( 後者を計算する_自然数 ( 後者を計算する_自然数 ( 足す_自然数 n_p o_p ) ) )
                    )
                .
            }
        }
    }
    {
        refine
            (
                match
                    n
                as
                    n_
                return
                    道@{ i }
                        自然数@{ i }
                        ( 足す_自然数 ( 足す_自然数 ( 後者を計算する_自然数 m_p ) n_ ) o )
                        ( 足す_自然数 ( 後者を計算する_自然数 m_p ) ( 足す_自然数 n_ o ) )
                with
                    零_構築子_自然数 => _ | 後者_構築子_自然数 n_p => _
                end
            )
        .
        {
            refine
                (
                    match
                        o
                    as
                        o_
                    return
                        道@{ i }
                            自然数@{ i }
                            ( 足す_自然数 ( 足す_自然数 ( 後者を計算する_自然数 m_p ) 零_自然数 ) o_ )
                            ( 足す_自然数 ( 後者を計算する_自然数 m_p ) ( 足す_自然数 零_自然数 o_ ) )
                    with
                        零_構築子_自然数 => _ | 後者_構築子_自然数 o_p => _
                    end
                )
            .
            {
                change
                    (
                        道@{ i }
                            自然数@{ i }
                            ( 足す_自然数 ( 足す_自然数 ( 後者を計算する_自然数 m_p ) 零_自然数 ) 零_自然数 )
                            ( 足す_自然数 ( 後者を計算する_自然数 m_p ) ( 足す_自然数 零_自然数 零_自然数 ) )
                    )
                .
                change ( 道@{ i } 自然数@{ i } ( 後者を計算する_自然数 m_p ) ( 後者を計算する_自然数 m_p ) ).
                exact ( 恒等道_道 自然数@{ i } ( 後者を計算する_自然数 m_p ) ).
            }
            {
                change
                    (
                        道@{ i }
                            自然数@{ i }
                            (
                                足す_自然数
                                    ( 足す_自然数 ( 後者を計算する_自然数 m_p ) 零_自然数 )
                                    ( 後者を計算する_自然数 o_p )
                            )
                            (
                                足す_自然数
                                    ( 後者を計算する_自然数 m_p )
                                    ( 足す_自然数 零_自然数 ( 後者を計算する_自然数 o_p ) )
                            )
                    )
                .
                change
                    (
                        道@{ i }
                            自然数@{ i }
                            ( 後者を計算する_自然数 ( 後者を計算する_自然数 ( 足す_自然数 m_p o_p ) ) )
                            ( 後者を計算する_自然数 ( 後者を計算する_自然数 ( 足す_自然数 m_p o_p ) ) )
                    )
                .
                exact
                    (
                        恒等道_道
                            自然数@{ i }
                            ( 後者を計算する_自然数 ( 後者を計算する_自然数 ( 足す_自然数 m_p o_p ) ) )
                    )
                .
            }
        }
        {
            refine
                (
                    match
                        o
                    as
                        o_
                    return
                        道@{ i }
                            自然数@{ i }
                            ( 足す_自然数 ( 足す_自然数 ( 後者を計算する_自然数 m_p ) ( 後者を計算する_自然数 n_p ) ) o_ )
                            ( 足す_自然数 ( 後者を計算する_自然数 m_p ) ( 足す_自然数 ( 後者を計算する_自然数 n_p ) o_ ) )
                    with
                        零_構築子_自然数 => _ | 後者_構築子_自然数 o_p => _
                    end
                )
            .
            {
                change
                    (
                        道@{ i }
                            自然数@{ i }
                            (
                                足す_自然数
                                    ( 足す_自然数 ( 後者を計算する_自然数 m_p ) ( 後者を計算する_自然数 n_p ) )
                                    零_自然数
                            )
                            (
                                足す_自然数
                                    ( 後者を計算する_自然数 m_p )
                                    ( 足す_自然数 ( 後者を計算する_自然数 n_p ) 零_自然数 )
                            )
                    )
                .
                change
                    (
                        道@{ i }
                            自然数@{ i }
                            ( 後者を計算する_自然数 ( 後者を計算する_自然数 ( 足す_自然数 m_p n_p ) ) )
                            ( 後者を計算する_自然数 ( 後者を計算する_自然数 ( 足す_自然数 m_p n_p ) ) )
                    )
                .
                exact
                    (
                        恒等道_道
                            自然数@{ i }
                            ( 後者を計算する_自然数 ( 後者を計算する_自然数 ( 足す_自然数 m_p n_p ) ) )
                    )
                .
            }
            {
                change
                    (
                        道@{ i }
                            自然数@{ i }
                            (
                                足す_自然数
                                    ( 足す_自然数 ( 後者を計算する_自然数 m_p ) ( 後者を計算する_自然数 n_p ) )
                                    ( 後者を計算する_自然数 o_p )
                            )
                            (
                                足す_自然数
                                    ( 後者を計算する_自然数 m_p )
                                    ( 足す_自然数 ( 後者を計算する_自然数 n_p ) ( 後者を計算する_自然数 o_p ) )
                            )
                    )
                .
                change
                    (
                        道@{ i }
                            自然数@{ i }
                            (
                                後者を計算する_自然数
                                    (
                                        後者を計算する_自然数
                                            ( 足す_自然数 ( 後者を計算する_自然数 ( 足す_自然数 m_p n_p ) ) o_p )
                                    )
                            )
                            (
                                後者を計算する_自然数
                                    (
                                        後者を計算する_自然数
                                            ( 足す_自然数 m_p ( 後者を計算する_自然数 ( 足す_自然数 n_p o_p ) ) )
                                    )
                            )
                    )
                .
                change
                    (
                        道@{ i }
                            自然数@{ i }
                            ( 二を足す_自然数 ( 足す_自然数 ( 後者を計算する_自然数 ( 足す_自然数 m_p n_p ) ) o_p ) )
                            ( 二を足す_自然数 ( 足す_自然数 m_p ( 後者を計算する_自然数 ( 足す_自然数 n_p o_p ) ) ) )
                    )
                .
                refine
                    (
                        関数を適用する_道
                            自然数@{ i }
                            自然数@{ i }
                            二を足す_自然数
                            ( 足す_自然数 ( 後者を計算する_自然数 ( 足す_自然数 m_p n_p ) ) o_p )
                            ( 足す_自然数 m_p ( 後者を計算する_自然数 ( 足す_自然数 n_p o_p ) ) )
                            _
                    )
                .
                refine
                    (
                        結合する_道
                            自然数@{ i }
                            ( 足す_自然数 ( 後者を計算する_自然数 ( 足す_自然数 m_p n_p ) ) o_p )
                            ( 後者を計算する_自然数 ( 足す_自然数 ( 足す_自然数 m_p n_p ) o_p ) )
                            ( 足す_自然数 m_p ( 後者を計算する_自然数 ( 足す_自然数 n_p o_p ) ) )
                            _
                            _
                    )
                .
                {
                    exact ( A_2024_01_25_0003 ( 足す_自然数 m_p n_p ) o_p ).
                }
                {
                    refine
                        (
                            結合する_道
                                自然数@{ i }
                                ( 後者を計算する_自然数 ( 足す_自然数 ( 足す_自然数 m_p n_p ) o_p ) )
                                ( 後者を計算する_自然数 ( 足す_自然数 m_p ( 足す_自然数 n_p o_p ) ) )
                                ( 足す_自然数 m_p ( 後者を計算する_自然数 ( 足す_自然数 n_p o_p ) ) )
                                _
                                _
                        )
                    .
                    {
                        refine
                            (
                                関数を適用する_道
                                    自然数@{ i }
                                    自然数@{ i }
                                    後者を計算する_自然数
                                    ( 足す_自然数 ( 足す_自然数 m_p n_p ) o_p )
                                    ( 足す_自然数 m_p ( 足す_自然数 n_p o_p ) )
                                    _
                            )
                        .
                        exact ( a m_p n_p o_p ).
                    }
                    {
                        refine
                            (
                                反転する_道
                                    自然数@{ i }
                                    ( 足す_自然数 m_p ( 後者を計算する_自然数 ( 足す_自然数 n_p o_p ) ) )
                                    ( 後者を計算する_自然数 ( 足す_自然数 m_p ( 足す_自然数 n_p o_p ) ) )
                                    _
                            )
                        .
                        exact ( A_2024_01_25_0002 m_p ( 足す_自然数 n_p o_p ) ).
                    }
                }
            }
        }
    }
Defined.

Definition 加算の交換法則_自然数@{ i | } ( m : 自然数@{ i } ) ( n : 自然数@{ i } )
    : 道@{ i } 自然数@{ i } ( 足す_自然数 m n ) ( 足す_自然数 n m )
.
Proof.
    refine ( let a := _ in a m n ).
    refine
        (
            fix a ( m : 自然数@{ i } ) ( n : 自然数@{ i } ) { struct m }
                : 道@{ i } 自然数@{ i } ( 足す_自然数 m n ) ( 足す_自然数 n m )
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
                道@{ i } 自然数@{ i } ( 足す_自然数 m_ n ) ( 足す_自然数 n m_ )
            with
                零_構築子_自然数 => _ | 後者_構築子_自然数 m_p => _
            end
        )
    .
    {
        refine
            (
                match
                    n
                as
                    n_
                return
                    道@{ i } 自然数@{ i } ( 足す_自然数 零_自然数 n_ ) ( 足す_自然数 n_ 零_自然数 )
                with
                    零_構築子_自然数 => _ | 後者_構築子_自然数 n_p => _
                end
            )
        .
        {
            change ( 道@{ i } 自然数@{ i } ( 足す_自然数 零_自然数 零_自然数 ) ( 足す_自然数 零_自然数 零_自然数 ) ).
            change ( 道@{ i } 自然数@{ i } 零_自然数 零_自然数 ).
            exact ( 恒等道_道 自然数@{ i } 零_自然数 ).
        }
        {
            change
                (
                    道@{ i }
                        自然数@{ i }
                        ( 足す_自然数 零_自然数 ( 後者を計算する_自然数 n_p ) )
                        ( 足す_自然数 ( 後者を計算する_自然数 n_p ) 零_自然数 )
                )
            .
            change ( 道@{ i } 自然数@{ i } ( 後者を計算する_自然数 n_p ) ( 後者を計算する_自然数 n_p ) ).
            exact ( 恒等道_道 自然数@{ i } ( 後者を計算する_自然数 n_p ) ).
        }
    }
    {
        refine
            (
                match
                    n
                as
                    n_
                return
                    道@{ i }
                        自然数@{ i }
                        ( 足す_自然数 ( 後者を計算する_自然数 m_p ) n_ )
                        ( 足す_自然数 n_ ( 後者を計算する_自然数 m_p ) )
                with
                    零_構築子_自然数 => _ | 後者_構築子_自然数 n_p => _
                end
            )
        .
        {
            change
                (
                    道@{ i }
                        自然数@{ i }
                        ( 足す_自然数 ( 後者を計算する_自然数 m_p ) 零_自然数 )
                        ( 足す_自然数 零_自然数 ( 後者を計算する_自然数 m_p ) )
                )
            .
            change ( 道@{ i } 自然数@{ i } ( 後者を計算する_自然数 m_p ) ( 後者を計算する_自然数 m_p ) ).
            exact ( 恒等道_道 自然数@{ i } ( 後者を計算する_自然数 m_p ) ).
        }
        {
            change
                (
                    道@{ i }
                        自然数@{ i }
                        ( 足す_自然数 ( 後者を計算する_自然数 m_p ) ( 後者を計算する_自然数 n_p ) )
                        ( 足す_自然数 ( 後者を計算する_自然数 n_p ) ( 後者を計算する_自然数 m_p ) )
                )
            .
            change
                (
                    道@{ i }
                        自然数@{ i }
                        ( 後者を計算する_自然数 ( 後者を計算する_自然数 ( 足す_自然数 m_p n_p ) ) )
                        ( 後者を計算する_自然数 ( 後者を計算する_自然数 ( 足す_自然数 n_p m_p ) ) )
                )
            .
            change
                (
                    道@{ i }
                        自然数@{ i }
                        ( 二を足す_自然数 ( 足す_自然数 m_p n_p ) )
                        ( 二を足す_自然数 ( 足す_自然数 n_p m_p ) )
                )
            .
            refine
                (
                    関数を適用する_道
                        自然数@{ i }
                        自然数@{ i }
                        二を足す_自然数
                        ( 足す_自然数 m_p n_p )
                        ( 足す_自然数 n_p m_p )
                        _
                )
            .
            exact ( a m_p n_p ).
        }
    }
Defined.
