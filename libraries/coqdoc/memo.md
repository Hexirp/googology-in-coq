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
