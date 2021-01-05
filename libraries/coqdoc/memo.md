# memo

CSS の作成においてのメモです。

## 構造

coqdoc が生成するドキュメントの構造をメモします。

* `body`
    * `div id="page"`
        * `div id="header"`
        * `div id="main"`
        * `div id="footer"`

`body` と `div id="page"` が二重になっているのは無駄でしょう。現在では `div id="header"` と `div id="main"` と `div id="footer"` は `header` と `main` と `footer` に置き換え可能でしょう。
