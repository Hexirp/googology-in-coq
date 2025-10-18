# 宇宙多相と累積性

```coq
Set Polymorphic Inductive Cumulativity.
```

これはどういう意味を持つのでしょうか。

その説明は [1][] ([1-archive][]) にありますが、最初は読む前に思考停止してしまっていました。

今日、丁寧に読んでようやく理解できたので、メモしておきます。

`i < j` の時に `List@{i} A` は `List@{j} A` へ変換できるでしょうか？ この場合は可能です。いわゆる covariant です。

しかし、通常の Coq では、ついさっきのような変換は不可能です。これを可能にするためのフラグが `Cumulative` です。

cumulative という名前が理解を阻害してしまっていたように感じます。 covariantness about universe level と言われていたら、 Scala の知識を持つ私ならすぐ理解できたと思います。

[1]: https://coq.inria.fr/refman/addendum/universe-polymorphism.html
[1-archive]: https://web.archive.org/web/20201018065808/https://coq.inria.fr/refman/addendum/universe-polymorphism.html
