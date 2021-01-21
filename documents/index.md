# document

googology-in-coq は、プログラム的に証明を書くことを目標としています。そのため、 Gallina としての項をソースコードから簡単に読み取れるような記述を維持しなければなりません。

## コーディング

本プロジェクトのスタイルと合わないため、標準ライブラリは使用しません。

`Set` と `Prop` は使いません。これは homotopy type theory の上に立って開発を行う際に障害になるためです。

帰納原理 (induction principle) の機能は、項をコントロールすることを困難にする上に、 `Set` と `Prop` を使うため、使用しません。次のような指定を Vernacular ファイルの最初で行ってください。

```
(** 帰納原理 (induction principle) を生成しないように設定します。 *)

Unset Elimination Schemes.
```

宇宙多相 (universe polymorphic) については必ず使用します。次のような指定を Vernacular ファイルの最初で行ってください。

```
(** 宇宙多相 (universe polymorphism) について設定します。 *)

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
```

タクティックは項のコントロールを困難にすることもありますが、有用であるため、限定的に使用します。詳細はタクティックの節を見てください。使用するときは、次のような指定を Vernacular ファイルの最初で行ってください。

```
(** タクティックが使用できるように設定します。 *)

Set Default Proof Mode "Classic".

(** ビュレットを使用しないときにエラーになるように設定します。 *)

Set Default Goal Selector "!".
```

カスタム表記 (notation) や暗黙引数 (implicit argument) や暗黙変換 (coercion) や型クラス (typeclass) などの機能は、項をコントロールすることを困難にするため、なるべく使いません。

定義における universe level については必ず明示的に記述してください。定義におけるレベルの制約は Coq がチェックしてくれるので、たとえ制約が空だとしても記述してください。 Gallina の式における宇宙のレベルは、それが型を返す関数であるときは記述してください。それ以外については自由です。

モジュールファイルの分け方の基準は、モジュールとしてどのようなものを提供するかという点に重きを置きます。

`Require Import` は使いません。モジュールファイルに対する操作である `Require` とモジュールに対する操作である `Import` では対象が異なるため、それを明確にしたいからです。

等式の補題について、両辺が余りにも巨大で理解しづらい時は、 Section 機能を使って、定義の分割をします。まず、引数を `Universe` と `Constriant` と `Context` を使って文脈に加えます。次に、両辺をそれぞれ一つの定義として記述します。この場合、普通は両方とも同じ型なので `foo_L` と `foo_R` という名前を付けることになります。最後に、この等式として `Path foo_L foo_R` という定理を証明します。ここで、この定理の名前は `L` と `R` の等式なので `foo_Path_L_R` という名前を付けます。

### コメント

定義の前には、それを簡単に説明するドキュメントとしてのコメントを付けます。定義を上手く分けられる時は coqdoc の見出し機能を使ってください。その直後には節の意味を説明するコメントをつける方がいいです。

```coq
(** ... *)

Definition foo a b c.

(** ... *)

Definition baa a b c.
```

ドキュメントとしてのコメントは、上記のように記述してください。 coqdoc が使う文芸的プログラミングの考え方に従って、ソースコードとドキュメントが対等になるように記述します。

coqdoc には見出し機能があり `(** * ... *)` は `h1` 要素に変換されますが、これは使わないでください。 `h1` 要素が coqdoc によりページの冒頭に追加されるので、 `h1` 要素が重複してしまうことになります。

定義の前には、それを説明する文章を書いてください。「……というようなものを定義する」という意味で「……です」だけ書いても構いません。

見やすくするため、ドキュメントの中にあるソースコードについては出来るだけ `[ ... ]` でソースコードとしての表示が行われるようにします。

定義の直前には、他のライブラリから引っ張ってきたものであるかどうかを区別するために `(* from: ... *)` というコメントを付けます。どこから定義を持ってきたのか、それとも誰かのオリジナルなのか、定義に手を加えたものであるかを判断できるようにします。

### 名前

モジュールの名前は、先頭を大文字にし、 camel case を使ってください。今は、セクションの名前には制限はありません。

関数や定理などの名前はポーランド記法を基本にしますが、良い名前があるときはそれを使って構いません。次に細かい慣習を示します。

* 関数が返すのが `Type` 型の値の時は先頭を大文字にする。
  * そうではないときは先頭を小文字にする。
* ポーランド記法を使わない時は camel case を使う。
* 依存型に対応したバージョンの関数は `D` を付けて表す。
  * 依存型に対応しないバージョンの関数は `N` を付けて表す。
  * これで表しきれない時は、その関数が受け取る型のそれぞれについて依存型かどうか調べて、適切な記号を付ける。
    * 依存型か非依存型の二分法。例は `compNND` など。
    * 二重の依存型が現れる時は `DD` とする。例は `trpt_D_DD_DD_DDD` など。
    * 依存関係をエンコードする。例は `ap011_AN_BDA_CN` など。
      * `A` が依存型ではない時は `_AN`
      * `B` が `A` に依存しているときは `_BDA`
      * `C` が `A` に依存しているときは `_CDA`
      * `C` が `B` に依存しているときは `_CDB`
      * `C` が `A` と `B` に依存しているときは `_CDAB`
* n 変数版とか n-道版というときには n を付ける。
* ポーランド記法を使う時は、
  * 区切り文字は `_` を使う。
  * `A -> B` は `fun_A_B` と書く。
  * `fun x => t` は `lam_x_t` と書く。
  * `A -> B -> ... Y -> Z` という形の時は `Z` と略せる。
  * `Path x y` という形の時は `x` と略せる。
  * `Path` は `p` と略せる。
  * `idpath` は `1` と略せる。
  * `conc p q` は `cpq` と略せる。
  * `inv p` は `vp` と略せる。
  * `trpt p u` は `T` と略せる。
  * `ap f p` は `afp` と略せる。
  * `ap f p` は `A` と略せる。
  * `p x` は `px` と略せる。
  * `p x` は `p` が点ごとの道であれば `P` と略せる。
  * ポーランド記法が入れ子になった時は `path_'conc_p_1'_p_q` という風にする。
  * 区別が付かないときは `_L` と `_R` を付けたりする。
  * `R foo_L foo_R` というときは `foo_R_L_R` としたりする。
  * 先頭に `'` が来たときは `_` を先頭に付けたりする。

宇宙のレベルの名前については、その役割が `i` より真に大きい値であるということである時は `si` と、その役割が `i` と `j` の最大値であるということである時は `mij` と、それぞれそのようにしてください。

### フォーマット

行が長すぎるときは、ちょうどよい区切りで改行してしてください。読みやすくするために字下げも行ってください。改行するのは 80 行が目安です。ただし、 coqdoc の仕様により開業するとスペースが挿入されてしまうため、ドキュメントとしてのコメントでは改行を行いません。

改行と字下げについての慣習を次に示します。改行すべき要素が括弧の中に入っていたり、他の規則によって既に字下げされている場合でも、最終的な分かりやすさのために、機械的に慣習に従うことが多いです。これらの規約は、一番外側の文から順番に適用してください。

```coq
(* Definition _ : _ := _. 0. *)
Definition foo _ : _ := _.

(* Definition _ : _ := _. 1. *)
Definition foo _ : _
  := _.

(* Definition _ : _ := _. 2. *)
Definition foo _
  : _
  := _.

(* Definition _ : _ := _. 3. *)
Definition foo
  _
  : _
  := _.

(* Definition _ : _ := _. 4. *)
Definition foo
  _ _ _
  _ _ _
  : _
  := _.

(* Definition _ : _ := _. 5. *)
Definition
  foo
  _ _ _
  _ _ _
  : _
  := _.

(* Definition _ : _. 0. *)
Definition foo _ : _.

(* Definition _ : _. 1. *)
Definition foo _
  : _.

(* Definition _ : _. 2. *)
Definition foo
  _
  : _.

(* Definition _ : _. 3. *)
Definition foo
  _ _ _
  _ _ _
  : _.

(* Definition _ : _. 4. *)
Definition
  foo
  _ _ _
  _ _ _
  : _.

(* forall x : T, P. 0. *)
forall x : T, P

(* forall x : T, P. 1. *)
forall x : T,
  P

(* forall x : T, P. 2. *)
forall
  _ _ _
  _ _ _,
  P

(* match _ as _ in _ return _ with _ end. 0. *)
match _ as _ in _ return _ with _ end

(* match _ as _ in _ return _ with _ end. 1. *)
match _
  as _
  in _
  return _
  with _
end

(* with _. 0. match 式の with 節に該当. *)
with _

(* with _. 1. match 式の with 節に該当. *)
with
  | _ => _
  | _ => _
  | _ => _

(* let _ := _ in _. 0. *)
let _ := _ in _

(* let _ := _ in _. 1. *)
let
  _ := _
in
  _

(* f x y. 0. *)
f x y

(* f x y. 1. *)
f
  x
  y
```

### タクティック

タクティックは、 Gallina の項をコントロールすることを困難にします。しかし、証明を段階的に行える利便性も大きいため、限定的に使用します。

Gallina の項をコントロールできるとして許容されているタクティックは次になります。

* `refine` タクティック
* `exact` タクティック（ただし、 Coq に組み込みの "ltac\_plugin" で定義されるタクティックのこと）
* `simpl` タクティック
* `cbv` タクティック
* `change` タクティック
* `move` タクティック
* `=>` タクティカル

さらに、新しく定義したタクティックも許されます。例えば、次のような例があります。

* `refine_conc` タクティック

ゴールが複数に増えたときはビュレットを使います。ビュレットは字下げせず、単独の行に置いてください。その後に続くコマンドは字下げしますが、一番後ろのゴールだけは字下げしなくともよいです。例として、次のようにします。

```
refine _.
- (* 字下げする *)
  exact x.
- (* 字下げしない *)
refine _.
+ (* 字下げする *)
  exact y.
+ (* 字下げする *)
  exact z.
```

`refine` でゴールが解消される時は、代わりに `exact` を使ってください。

ゴールを最後まで評価して、 `Path idpath idpath` というような項まで落とす時は、 `cbv` を使ってください。ゴールの一部分だけを単純にしたい場合は `simpl` を使ってください。この二つでどうにもならないときは `change` を使ってください。

`refine` で let 式を使い、仮定をゴールに戻すときは、空行を空けることを検討してください。

## ビルド

ビルドは shell ファイルを使って行います。

Coq では Makefile を使うのがスタンダードのようなのですが、 Makefile を自動生成するためのファイルがあったり、そのためのツールがあったりと、複数の層があって訳が分からない上に、 Windows で使うことが困難なようなので、取り敢えずは shell ファイルを使っています。

### build.sh

`files.sh` に記述されたファイルを対象にして、コンパイルを行います。標準ライブラリを使用しないために `-nois` を、詳細なログを出力させるために `-verbose` を、モジュールの構成のために `-R theories/ GiC` を、それぞれ `coqc` のオプションに与えています。

生成する物は次の通りです。

* `theories/[x0]/[x1]/.../[xn].v` から生成される物
  * `theories/[x0]/[x1]/.../.[xn].aux`
  * `theories/[x0]/[x1]/.../[xn].glob`
  * `theories/[x0]/[x1]/.../[xn].vo`
  * `theories/[x0]/[x1]/.../[xn].vok`
  * `theories/[x0]/[x1]/.../[xn].vos`

### coqc.sh

`coqc` のラッパーです。これを参照することで、別の環境でも、このファイルを書き換えるだけで対応できるようになっています。

### coqdoc.sh

`coqdoc` のラッパーです。これを参照することで、別の環境でも、このファイルを書き換えるだけで対応できるようになっています。

### coqide.sh

`coqide` のラッパーです。これを参照することで、別の環境でも、このファイルを書き換えるだけで対応できるようになっています。

### edit.sh

プロジェクトの編集を開始します。標準ライブラリを使用しないために `-nois` を、モジュールの構成のために `-R theories/ GiC` を、それぞれ `coqide` のオプションに与えています。

これを使うと、標準ライブラリとの名前の衝突が発生せず、 `Require GiC.Base.` というような記述が正常に動作します。

### files.sh

コンパイルやドキュメントの生成などの対象となるファイルを記述します。 `foo.v baa.v ` という風にファイルと空白が交互に出力されます。

### make\_document.sh

`files.sh` に記述されたファイルを対象にして、プロジェクトのコメントによるドキュメントを生成します。日本語でも正常に動作させるために `-utf8` を、生成先として `docs/` を指定するために `-d docs/` を、モジュールの構成のために `-R theories/ GiC` を、それぞれ `coqdoc` のオプションに与えています。

生成する物は次の通りです。

* `coqdoc.css`
* `index.html`
* `theories/[x0]/[x1]/.../[xn].v` から生成される物
  * `docs/[x0].[x1].....[xn].html`

## デバッグ

正しいはずの場所でエラーが起きたり、誤っているはずの場所でエラーが起きなかったりして、その原因が分からない場合は、最終手段として "View" タブの "Display all low-level contents" が使えます。

## モジュール

モジュールについての全体から見た役割を記述します。 libraries.gv はモジュールの依存関係と性質を示しています。

### GiC.Base

次のゴールがあるとします。

```
______________________________________(1/1)
Path@{i} x z
```

これを次のように分割したいとします。

```
______________________________________(1/2)
Path@{i} x y
______________________________________(2/2)
Path@{i} y z
```

そんな時は、次のように書きます。

```
refine (conc _ (_ : Path@{i} y _)).
```

これは `GiC.Path.Base` で `refine_conc y` としてタクティック化されています。

### GiC.Path

`ap10` と `ap1D0` などには、宇宙多相において `max` を取るパターンを含みます。これに関して宇宙制約の書き方を間違えると `Universe constraints are not implied by the ones declared.` とだけの分かりづらいエラーメッセージが出ます。そのため、原因が分かりづらく、注意が必要です。実際に、私は `GiC.Path` の `ap10` と `ap1D0` を扱う部分において苦労しました。

作者でも全ての定理を覚えられていません。ここの定理を探すには `SearchPattern` を使うことを推奨します。

現在の内容は https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v をベースにしています。

頻出するパターンとして `refine (match p with idpath => _ end).` があります。

## 開発

コミットメッセージのタイトルには「何を」変更したかを書いてください。本文には「どうして」変更したかを書いてください。この変更が未来に無意味になったり問題になったりするかもしれないという時は、それも書いてください。

コミットメッセージが 50 文字を超えてしまうことを恐れないでください。単語の数の方が重要な基準です。

git のコミットは、その意味に沿って、可能な限り、病的に、分割してください。そうすると、 cherry-pick を使ってコンフリクトを起こさせないようにすることも可能です。

ブランチは木構造として上下関係を設定します。 master ブランチが上で working/0 ブランチは下という風に考えます。

下のブランチを上のブランチにマージしようとすると、コンフリクトが起こる可能性があります。この時は、上のブランチを下のブランチにマージしてコンフリクトを解消してください。

もし A というブランチを再構成したい場合は、新しいブランチを切ります。このブランチの名前は自由ですが、説明のために A' という仮の名前を付けます。そして、 A' に A の変更を cherry-pick などで取り込みます。ここで A' に取り込むべき細かい変更が残っている場合は master ブランチへ cherry-pick します。そして、 A' ブランチを master ブランチにマージした後に、取り込まない変更を切り捨てるために A ブランチを ours 戦略でマージします。この方法は、二つ以上のブランチへ再構成する時も適用可能です。もし、 A と A' を完全に一致させられるのなら octopus 戦略も使えます。

もし、ブランチの役割にそぐわない細かい変更をコミットした時は、すぐに master ブランチへ cherry-pick してください。

merge request は、マージする時にワンクッションを置きたい場合に作成してください。それをマージする前に、変更を取り込ませるブランチを変更が取り込まれるブランチにマージしてください。

merge する時は no fast forward としてください。ただし、 git pull の時は例外です。

rebase は、なるべく使わないでください。ただし、 git pull で変更が少ない時は例外です。

`B` から `A` への merge request を自動的にマージ出来るときは、次の場合です。

* fast-forward である。
* approved である。
* CI が通っている。

## バージョニング

Semantic Versioning を採用します。現在は基本的に `0.x.y` を付け、設計が確定するまで多くの変更を行う予定です。

## 訳語

紛らわしい単語たちの訳語を一つに定めます。

[Is equality the same as identity?](https://math.stackexchange.com/questions/128778/is-equality-the-same-as-identity) を参考にする。

* equation - 方程式 - 自由変数の値によっては両辺が等しくないかもしれず、自由変数の値に制約を掛ける等式である。
* identity - 恒等式 - 自由変数の値に関わらず常に等しい等式である。

[What is the difference between identity and equality in OOP](https://stackoverflow.com/questions/1692863/what-is-the-difference-between-identity-and-equality-in-oop) と [等価性の比較と同一性](https://developer.mozilla.org/ja/docs/Web/JavaScript/Equality_comparisons_and_sameness) を参考にする。

* identity - 同一性 - 同じインスタンスであること。
* equality - 等価性 - 値が等しいこと。

[identity type](https://ncatlab.org/nlab/show/identity+type) を参考にする。

* identity type - 等式型 - ある値とある値が等しいことを示す型。
* equality type - 等式型 - ある値とある値が等しいことを示す型。

HoTT Book を参考にする。

* identity - equality とあまり区別はされない。 identity type と関連したところで多く使われる。 identity function で恒等関数を指すこともある。
* equality - identity とあまり区別はされない。 等式そのものを指して equality と言ったり、 judgmental equality とか definitional equality とか propositional equality という風に、形容詞を付けて出てくることも多い。
* equivalence - 二つの型の間に定義される等しさ。
* homotopy - 連続的に移り合うものについてのいろいろ。

一般的な訳を参考にする。

* topology - 位相幾何学
* homotopy - ホモトピー

様々な熟語を並べてみる。

* 同一
* 同形
* 同相
* 同価
* 同型
* 同値
* 相同
* 相似
* 等しさ
* 等価
* 等値

homotopy は頻繁に出てくる単語であるにもかかわらず、翻訳がホモトピーしかないのはおさまりが悪い。

[homotopy](https://en.wiktionary.org/wiki/homotopy) を参考にする。

* homotopy - From Ancient Greek ὁμός (homós, “same, similar”) + τόπος (tópos, “place”); earliest known use in print in 1922, Oswald Veblen, Analysis Situs.

homotopy の訳を定める。

* homotopy - 類位

equivalence は頻繁に出てくる単語であるにもかかわらず、訳語が equality と重複する「等価」しかない。

equality は一般的な等しさを表し identity は homotopy type theory の中の概念である identity type と結びつくことが多い。

equivalence の訳を定める。

* equivalence - 等価

等価といったら equivalence であると定める。

## 歴史

歴史を簡単にまとめます。

* https://github.com/Hexirp/googology-in-coq/commit/4df41c2a3fd66114f16de4dba1859d7f42fd667a - 一代目の Main.v が追加される。
* https://github.com/Hexirp/googology-in-coq/commit/0e89ce558fc7f57c75c9a384844f1c655d600b8a - 一代目の Main.v が OldMain.v へリネームされる。
* https://github.com/Hexirp/googology-in-coq/commit/06eab1805dca316cd726885eafbac04f1dfcb1c0 - 現在の Base.v の大部分が二代目の Main.v として追加される。
* https://github.com/Hexirp/googology-in-coq/commit/58ad7a0963ad4b88910a6b102475d8e184d5d8d0 - 二代目の Main.v が Core.v へリネームされる。自然数に関するコードが三代目の Main.v として追加される。
* https://github.com/Hexirp/googology-in-coq/commit/07f1b9203703ef9fe6f8f656763991f695529028 - 現在の "GiC" としてのプロジェクトが開始される。
* https://github.com/Hexirp/googology-in-coq/commit/d5e6fafe67991bdd8ef0dfcef2076d1d80f1fef2 - 道に関するコードが三代目の Main.v に代わって四代目の Main.v として追加される。
* https://github.com/Hexirp/googology-in-coq/commit/b3612d1cfb3c846c3b4e7231b94b7480f456b5c0 - たとえ内容が一言であったとしてもドキュメントを書くということが始められる。
* https://github.com/Hexirp/googology-in-coq/commit/ce65540a3004730135c1a0015f55397b963ec028 - 単語の意味とモジュールの役割について考察した結果に従い、 Core.v が現在の Base.v にリネームされる。
* https://github.com/Hexirp/googology-in-coq/commit/33d28c102388973db6583b78f542070c18ace06c - 複雑化する証明に対処することを目的として Coq と SSReflect の Ltac の使用が開始された。
* https://github.com/Hexirp/googology-in-coq/commit/8502cc01c69ef66a90e4dd9c43ed58b47f54fd77 - ファイルの位置付けを行うための GraphViz ファイルが追加される。
* https://github.com/Hexirp/googology-in-coq/commit/67c9d66ccc1670e0ae0f09437f16716ed04c1e3f - ソースコードの内部に書かれるドキュメントでは、利用者の視点に立ったドキュメントを書けないという考えに従い、外部からのドキュメントとして document/ フォルダが作られる。
* https://github.com/Hexirp/googology-in-coq/commit/bfcf9f4d42a5d5177788c607d9b43d59b1f6d23a - 使用するプラグインを GiC 全体で一貫させるために、 GiC.Base でプラグインの読み込みを行うようになる。
* https://github.com/Hexirp/googology-in-coq/commit/6e45860f945debb7d99f0a9902e64dae2179df3b - 宇宙のレベルの制約を Coq にチェックさせるために、制約を必ず書くことが始められる。
* https://github.com/Hexirp/googology-in-coq/commit/e9d27ed9a1cc15848dcbaf9d01707ebff528b3c5 - ドキュメントのチェックのために coqdoc の使用が開始される。
* https://github.com/Hexirp/googology-in-coq/commit/89d432c82e32e0be5d0d3a894a68c322baa5bf15 - coqdoc が使えるようになったため、ファイルの構造が分かりやすいように、セクション機能を利用するようになる。
* https://github.com/Hexirp/googology-in-coq/commit/34cbcda37abceef8f06ad2c2b7a7e43fb1587d0d - Base.v と 四代目の Main.v を元にして詳細な命名規則が記述される。
* https://github.com/Hexirp/googology-in-coq/commit/27ae14f9b5ad1cb2b2e71473691b23c016c53820 - Base.v と四代目の Main.v を元にして詳細な改行と字下げの規則が記述される。
* https://github.com/Hexirp/googology-in-coq/commit/9e0be8dde2927104fc51a0be805be1ba0fb42a61 - shell ファイルが整理され、それぞれの役割が明確になった。
* https://github.com/Hexirp/googology-in-coq/commit/3d7f2c0d0417f0bd9a7c7376c42e13e575034ff1 - ドキュメントに詳細な節が導入されて構造が分かりやすくなった。
* https://github.com/Hexirp/googology-in-coq/commit/abcb0ac369875055c50748796e8a973d162caaf5 - 型を単純化して理解を容易にするために Section 機能の使用が開始される。
* https://github.com/Hexirp/googology-in-coq/commit/ddf470fbd874d386d86ff2e79c9a4145bc1ce3ab - 別のライブラリを参考にした定理が分かるように、定理の由来をコメントに書くようになる。
* https://gitlab.com/Hexirp/googology-in-coq/-/commit/2e052992be3144af771d464988196a2bcedde48c - Git のリポジトリのホスティングに使うサービスを GitHub から GitLab へ変更しました。
* https://gitlab.com/Hexirp/googology-in-coq/-/commit/afad3b7afbe7309dafc6c7cf903567bc5c3f1dff - ドキュメントの書き方について、より読みやすくなるように規約を定めなおした。
* https://gitlab.com/Hexirp/googology-in-coq/-/commit/740c03e0aae782b176dacb8cb4d3dff4488acc34 - Everything モジュールのパターンを使い始めた。
* https://gitlab.com/Hexirp/googology-in-coq/-/commit/c3a7bef293e0920453e20c45c3e45cf63301c0bd - インデントについてのコーディングスタイルを厳密にした。
* https://gitlab.com/Hexirp/googology-in-coq/-/commit/0a9c0be392a5eb26377c244ec9bce44b31157a13 - HoTT.Basics.PathGroupoids の移植を完了させた。
