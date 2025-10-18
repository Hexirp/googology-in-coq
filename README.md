# googology-in-coq

Coq を使用して巨大数論を形式化することができないか試みていたプロジェクトであり、現在は [dekatlas](https://github.com/Hexirp/dekatlas) に移行しています。 Coq を使用して数学を形式化するというプロジェクトとして解釈するならば [seityou](https://github.com/Hexirp/seityou) の後継となりますが、このプロジェクトの特色は巨大数論に焦点を絞り込んでいたことです。

## archive

googology-in-coq は何回も作り直しているため、アーカイブするにあたり、それらの古いコードをすぐに見つけることができるように、それぞれのフォルダに配置しています。

### archive-2020-05

最も古いバージョンです。まだ通常の Coq のライブラリと近いスタイルですが、項の構造を明瞭にするということへの執着と、 `{` と `}` の使用とポーランド記法による名付けを既に観察することができます。

### archive-2021-05

二番目に古いバージョンです。 [Coq-Hott](https://github.com/HoTT/Coq-HoTT/tree/7b1b46057f97866a0c27678940bd1333984b79fc) を再構成しており、特に [PathGroupoid](https://github.com/HoTT/Coq-HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v) における定理を全て実装しています。ここからコーティングスタイルと coqdoc によるドキュメントの生成と shell スクリプトによるビルドシステムと GitLab CI による自動ビルドシステムを導入しています。

### archive-2022-03

三番目に古いバージョンです。暗黙引数を廃止し、最小限の inductive types を使用して可能な限り広いモデルで成り立つようにするスパルタ方式を導入して、作り直しています。ここから GitHub Actions による自動ビルドシステムを導入しています。

### archive-2023-04

四番目に古いバージョンです。スパルタ方式を廃止して作り直しています。ここから GitHub Actions の環境に限り opam によるビルドシステムを導入しています。

### archive-2024-02

五番目に古いバージョンです。 "[Introduction to Homotopy Type Theory](https://arxiv.org/abs/2212.11082)" を再構成しています。早すぎる分割を抑えるために一つのファイルにまとめて作り直しています。ここから日本語による名付けと日付と連番による名付けを導入しています。

### archive-2024-10

六番目に古いバージョンです。 "[Introduction to Homotopy Type Theory](https://arxiv.org/abs/2212.11082)" を再構成しており、特に第 1 部 "Martin-Löf’s Dependent Type Theory" の第 4 章 "More inductive types" までの演習問題の解を全て実装しています。ここからモジュールによる区分を導入しています。
