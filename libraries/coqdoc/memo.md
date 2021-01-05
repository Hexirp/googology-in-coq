# memo

CSS の作成においてのメモです。

## 構造

coqdoc が生成するドキュメントの構造をメモします。

* `body`
    * `div id="page"`
        * `div id="header"`
        * `div id="main"`
        * `div id="footer"`

`body` と `div id="page"` が二重になっているのは無駄でしょう。 HTML 5 では `div id="header"` と `div id="main"` と `div id="footer"` は `header` と `main` と `footer` に置き換え可能でしょう。

* `div id="footer"`
    * `hr`
    * `Index` へのリンク
    * `hr`
    * coqdoc で生成されたドキュメントであることを説明する文章

ここは別に問題はありません。しいて言えば、最初の `hr` は `div id="main"` と `div id="footer"` の間に挟み込むようにした方が美しい形になると思います。

* `div id="main"`
    * `h1 class="libtitle"`
        * ライブラリの名前
    * `div class="code"`
        * ソースコード
    * `div class="doc"`
        * ドキュメント
    * `div class="code"` と `div class="doc"` の繰り返し……

`h1 class="libtitle"` は `div id="header"` (`header`) に置く方がいいように思いますが、まあ問題はないでしょう。 `div class="code"` と `div class="doc"` が交互に入れ替わって表示される形式なのは残念な所です。 `haddock` や `rustdoc` のように定義にドキュメントが付随するという形の方が良かったです。とはいえ、全てが命名的なコマンドである Coq (Vernacular) の事情に加えて、文芸的プログラミング (literate programming) の考え方を実践しているようなので、この点を責めるのは酷でしょう。

```coq
(* Run with -nois. *)

(** * GiC.Base *)

(** [GiC.Base] は、全ての基礎となる型や関数などを定義します。

    具体的には、一階述語論理に対応する型と、それに関する本当に単純な関数を提供しています。
 *)
```

私はいつも冒頭に上記のような記述を加えています。この記述のコンパイル結果が問題です。

```html
<h1 class="libtitle">Library GiC.Path.Base</h1>

<div class="code">

<br>
</div>

<div class="doc">
<a id="lab3"></a><h1 class="section">GiC.Path.Base</h1>

<div class="paragraph"> </div>

 <span class="inlinecode"><span class="id" title="var">GiC.Path.Base</span></span> は道に関する基本的な定義を提供します。

<div class="paragraph"> </div>

    具体的には、よく現れるパターンを一般化したタクティックや、 <span class="inlinecode"><span class="id" title="var">GiC.Base</span></span> にある関数の単純なバリエーションなどを定義します。

<div class="paragraph"> </div>

 必要なライブラリを要求します。
</div>
```

上記のようにコンパイルされます。

```html
<div class="code">

<br>
</div>
```

この個所に注目してください。 `(* Run with -nois. *)` というようなコメントが一つのコードとして見なされてしまっているようなのです。このせいで不自然な空白が空いてしまいます。

また、先ほど `h1 class="libtitle"` についてコメントしましたが、この `h1` タグが `<a id="lab3"></a><h1 class="section">GiC.Path.Base</h1>` と重複してしまっています。本来は `h1` の重複は避けるべきなのですが、 coqdoc はその辺りのことを汲んではくれないようです。

* `div class="code"`
    * ソースコード - `span class="id" title="foo"` で、色を付けるべき箇所であることを指定し `foo` で色の種別を指定している。その上から `a class="idref" href="foo"` で `foo` へリンクするべき要素であることを指定している。 `br` タグで改行を行っている。

シンタックスハイライトの実現の仕方については問題ないでしょう。 `br` タグを使っていることが大きな問題です。ソースコードを表現するためには `pre` タグと `code` タグの組み合わせを使うか、最低限でも `pre` タグを使うべきでしょう。

* `span class="id" title="foo"`

上記での `foo` の種別は何があるのでしょうか。 [coqdoc.css](https://github.com/coq/coq/blob/a22da3e70551658deefbbedf261acdc3ead5403d/tools/coqdoc/coqdoc.css#L162-L218) を見てみましょう。

```css
/* Identifiers: <span class="id" title="...">) */

.id { display: inline; }

.id[title="constructor"] {
    color: rgb(60%,0%,0%);
}

.id[title="var"] {
    color: rgb(40%,0%,40%);
}

.id[title="variable"] {
    color: rgb(40%,0%,40%);
}

.id[title="definition"] {
    color: rgb(0%,40%,0%);
}

.id[title="abbreviation"] {
    color: rgb(0%,40%,0%);
}

.id[title="lemma"] {
    color: rgb(0%,40%,0%);
}

.id[title="instance"] {
    color: rgb(0%,40%,0%);
}

.id[title="projection"] {
    color: rgb(0%,40%,0%);
}

.id[title="method"] {
    color: rgb(0%,40%,0%);
}

.id[title="inductive"] {
    color: rgb(0%,0%,80%);
}

.id[title="record"] {
    color: rgb(0%,0%,80%);
}

.id[title="class"] {
    color: rgb(0%,0%,80%);
}

.id[title="keyword"] {
 color : #cf1d1d;
/*     color: black; */
}
```

長々と失礼しました。これらのクラスに対して記述していけば大丈夫でしょう。

* `div class="doc"
    * コメントに記述した文章が空行ごとに区切られたもの
    * `<div class="paragraph"> </div>`
    * コメントに記述した文章が空行ごとに区切られたものなどが、 `div class="paragraph"` を挟んで繰り返される……

`div class="doc"` を見てみます。すると、上記のような記述になっていました。非常に酷い記述です。段落は `p` タグで囲む必要があるのはいうまでもなく、 HTML のタグを CSS 的に使っています。その名前も `paragraph` という名前になっており、実情と合っていません。 ` ` と空白を挟んでいるのは、削除されたりするのを回避するためなのでしょうが、素直に言って汚いです。
