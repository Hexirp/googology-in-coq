# 変更記録

## まだリリースされていない変更

`GiC.Type.Nat` ライブラリを追加しました。自然数を取り扱うライブラリです。

## 0.1.2

* [Commit ID][commit-v0.1.2]

[commit-v0.1.2]: https://gitlab.com/Hexirp/googology-in-coq/-/commit/eddaf097c31849b6c4f4d9ce1da3704ff8290103

`Fiber` を追加しました。 Homotopy Type Theory における重要な概念です。

`PwPath` と `PwPathN` を追加しました。 Homotopy Type Theory における重要な概念です。

`IsEquiv` と `Equiv` を追加しました。 Homotopy Type Theory における重要な概念です。

`IsProp` と `IsSet` を追加しました。 Homotopy Type Theory における重要な概念です。

`refine_conc` を `refine_by_conc` に名前変更しました。タクティックが何をするのか分かりやすくなりました。

## 0.1.1

* [Commit ID][commit-0.1.1]

[commit-0.1.1]: https://gitlab.com/Hexirp/googology-in-coq/-/commit/a5a553353d0b5f9464a6966ccee4e99447dd2700

`path_elim` というタクティックを追加しました。これは `refine (match p with idpath _ end)` を `path_elim p` という形で短縮するものです。

* [Path に対するパターンマッチングをタクティックとして切り出す][issue-2]
* [Path に対するパターンマッチングをタクティックとして切り出す][request-6]

[issue-2]: https://gitlab.com/Hexirp/googology-in-coq/-/issues/2
[request-6]: https://gitlab.com/Hexirp/googology-in-coq/-/merge_requests/6

## 0.1.0

* [Commit ID][commit-v0.1.0]

[commit-v0.1.0]: https://gitlab.com/Hexirp/googology-in-coq/-/commit/0dfec356061093a1288ac16d123570edecb7f1d4

確固としたコーディングスタイルに従って、ライブラリとドキュメントを作成しました。

```text
GiC.Base
GiC.Function
GiC.Path.Base
GiC.Path.Function
GiC.Path.OneDim
GiC.Path.TwoDim
GiC.Path.Transposition
GiC.Path.Functoriality
GiC.Path.Application_1_0
GiC.Path.Application_1_1
GiC.Path.Transport
GiC.Path.Fibration
GiC.Path.Transport_2
GiC.Path.Application_D
GiC.Path.Application_0_2
GiC.Path
GiC.Type.Base
```

上記のライブラリを追加しました。

```text
compile.sh
coq_path.sh
coqc.sh
coqdoc.sh
coqide.sh
edit.sh
files.sh
make_document.sh
```

上記の shell スクリプトを追加しました。

```text
index.md
libraries-tred.gv
libraries.gv
```

上記のドキュメントを追加しました。

GitLab CI/CD を導入しました。継続的にテストを行うことで作業を一つのブランチに集約しても不都合が起きにくいシステムを構築しました。 coqdoc で生成したドキュメントを GitLab Pages を使って公開するようにしました。

## 0.0.0

* [Commit ID][commit-v0.0.0]

[commit-v0.0.0]: https://gitlab.com/Hexirp/googology-in-coq/-/commit/ac7eb156aac3804e8f2f52c54943fc6d6b6d083d

最初のバージョンであり、どのようなコードも含まれていません。
