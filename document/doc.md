# document

構成的にするために Gallina の項を重視します。そのため、たとえタクティックを使う場合でも、項がコントロールできるように注意してください。

今のところ許容されているタクティックは次になります。

* `refine` タクティック
* `=>` タクティカル
* `exact` タクティック（ただし、一つの項を引数として与えた時のみ）

ゴールが複数に増えたときはビュレットを使います。ビュレットは字下げせず、単独の行に置いてください。その後に続くコマンドは字下げしますが、一番後ろのゴールだけは字下げしなくともよいです。例として、次のようにします。

```
-
  exact x.
-
refine _.
+
  exact y.
+
  exact z.
```

`refine` でゴールが解消される時は、代わりに `exact` を使ってください。

関数や定理などの名前はポーランド記法を基本にしますが、良い名前があるときはそれを使って構いません。次に細かい慣習を示します。

* 関数が返すのが `Type` 型の値の時は先頭を大文字にする。
* そうではないときは先頭を小文字にする。
* 依存型に対応している版の関数は `D` を付けて表す。
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
  * `ap f p` は `A` と略せる。
  * `p x` は `p` が点ごとの道であれば `P` と略せる。
  * ポーランド記法が入れ子になった時は `path_'conc_p_1'_p_q` という風にする。
  * 区別が付かないときは `L` と `R` を付けたりする。

行が長すぎるときは、ちょうどよい区切りで改行してしてください。読みやすくするために字下げも行ってください。

改行と字下げについての慣習を次に示します。改行すべき要素が括弧の中に入っていたり、他の規則によって既に字下げされている場合でも、最終的な分かりやすさのために、機械的に慣習に従うことが多いです。

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

(* forall x : T, P. 0. *)
forall x : T, P

(* forall x : T, P. 1. *)
forall x : T,
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

定義における宇宙のレベルについては必ず記述してください。定義におけるレベルの制約は Coq がチェックしてくれるので、たとえ制約が空だとしても記述してください。式における宇宙のレベルは、型を返す関数であるときは記述してください。それ以外については自由です。

## GiC.Core

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

## GiC.Path

作者でも全ての定理を覚えられる自信がないので、 `SearchPattern` を使うことを推奨します。

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
