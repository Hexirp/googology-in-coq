# googology-in-coq

Coq を使用して巨大数論を形式化できないか試みていたプロジェクトであり、現在は [dekatlas](https://github.com/Hexirp/dekatlas) に移行しています。 Coq を使用して数学を形式化するというプロジェクトとして解釈するならば [seityou](https://github.com/Hexirp/seityou) の後継となりますが、このプロジェクトの特色は巨大数論に焦点を絞り込んでいたことです。

## archive

googology-in-coq は何回も作り直しているため、アーカイブするにあたり、それらの古いコードをすぐに見つけることができるように、それぞれのフォルダに配置しています。

### archive-2020-05

最も古いバージョンです。まだ通常の Coq のライブラリに近いスタイルですが、演算子の使用の拒絶と、項の構造を明瞭にするということへの異常な執着と、広範な `{` と `}` の使用と、ポーランド記法による名付けを、既に観察することができます。

### archive-2021-05

二番目に古いバージョンです。当時の [Coq-HoTT](https://github.com/HoTT/Coq-HoTT/tree/7b1b46057f97866a0c27678940bd1333984b79fc) を途中まで再構成しており、特に当時の [PathGroupoid](https://github.com/HoTT/Coq-HoTT/blob/7b1b46057f97866a0c27678940bd1333984b79fc/theories/Basics/PathGroupoids.v) にある定理を全て実装しています。ここからコーティングスタイルと coqdoc によるドキュメントの生成と shell スクリプトによるビルドシステムと GitLab CI による自動ビルドシステムを導入しています。

### archive-2022-03

三番目に古いバージョンです。暗黙引数の使用を廃止し、最小限の帰納型のみを使用するスパルタ方式を導入して、作り直しています。ここから GitHub Actions による自動ビルドシステムを導入しています。

### archive-2023-04

四番目に古いバージョンです。スパルタ方式を廃止して作り直しています。ここから GitHub Actions の環境に限り opam によるビルドシステムを導入しています。

### archive-2024-02

五番目に古いバージョンです。当時の "[Introduction to Homotopy Type Theory](https://arxiv.org/abs/2212.11082)" (Egbert Rijke, 2022) を途中まで再構成しています。早すぎる分割を抑えるために一つのファイルにまとめて作り直しています。ここから日本語による名付けと日付・連番による名付けを導入しています。

### archive-2024-10

六番目に古いバージョンです。当時の "[Introduction to Homotopy Type Theory](https://arxiv.org/abs/2212.11082)" (Egbert Rijke, 2022) を途中まで再構成しており、特に第 1 部 "Martin-Löf’s Dependent Type Theory" の第 4 章 "More inductive types" までの演習問題の解を全て実装しています。ここから入れ子のモジュールと例外なき日付・連番による名付けと別名システムを導入しています。
