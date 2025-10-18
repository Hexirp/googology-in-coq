# googology-in-coq

巨大数論を Coq で形式化します。

## 方針

googology-in-coq は、他のプロジェクトにはない独自の方針を持ちます。

* ある定義がどのような Gallina の項を生成するのかを直感的に判別できるようにする。
* 定義自体は同じだが意味が異なる二つの概念を混合しないようにする。それぞれの側面に応じた名前を付ける。
* Homotopy Type Theory の知見を取り入れる。 `Set` と `Prop` を使用しない。
* 日本語で開発を行う。開発の過程は可能な限り文書化する。

## 構成

プロジェクトは、いくつかの部分に分かれています。

* [articles/](./articles/README.md) - プロジェクトに関する記事です。
* [documents/](./documents/README.md) - プロジェクトのドキュメントです。
* [libraries/](./libraries/README.md) - プロジェクトのソースコードです。

## ドキュメント

coqdoc により自動生成されたドキュメントが [GitLab Pages](https://hexirp.gitlab.io/googology-in-coq/) にて利用できます。
