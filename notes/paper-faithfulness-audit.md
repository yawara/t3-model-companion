# 原稿と形式化の対応

2026-09-10。対象は `T3_modelcompanion_v4.tex`。
原稿 SHA256 は `79745dfa1660a827c51ec3c6b2006ee9d6243cb4702f97a75e5b55357b89f50b`。
原稿の著者は Yawara Ishida、Ryosuke Mizuno、Kota Takeuchi、形式化の著者は Yawara Ishida。

## 照合する内容

[論文対応表](../docs/paper-map.md)は、50数学項目・75部分項目について、原稿の所在、
公開宣言、Lean の証明状態、原稿との照合状態を別々に記録する。
照合は AI agents による原稿・型・主要構成の読解であり、自然言語の意味の機械的認証や
人間による独立査読を意味しない。

- 指数は3を割る条件で、自明群を含める。
- 自由群と coproduct は任意 rank を扱い、無限 rank では有限支持を用いる。
- `t(n) = n + n.choose 2 + n.choose 3`、`f₀(n) = 15*n^2`、
  `f(m) = f₀((3*m+4)*t(m)+1)` を原稿どおり定義する。
- graded の商・非斉次関係・混合 tensor block の符号を保持する。
- strictification は同時 root quotient と欠損商の基底を使い、原稿の生成元上界を得る。
- amalgamation は共通部分上の一致を要求する通常の条件とする。
- 一般モデル理論の定義には任意宇宙への bridge を設ける。

一つの補助的な degree-one 比較には、普遍性と retraction による直接証明を用いる。
主要な自由表示・block quotient・root・strict envelope・support の経路は原稿に従う。
原稿の仮定や上界を変更した主張として登録しない。

## 検証記録

原稿の数学的読解は [数学的検証](paper-mathematical-audit.md)、完成したライブラリの
数学的範囲と符号化は [完成記録](paper-faithful-completion.md)に記す。
各時点の機械検証は対応表が指す入力 revision と検証記録に限定される。
履歴上の検証成功から、変更後のソースの検証成功を推定しない。

Palomar の独立した statement comparison は [登録準備](../docs/palomar.md)に記す。
その選択対象は Theorem 3.3 と Corollary 3.4 であり、論文全項目の自然言語照合とは区別する。
