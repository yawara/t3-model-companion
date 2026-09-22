# 原稿と形式化の対応

2026-09-22。現行の出典は [T3_modelcompanion_v7.tex](../T3_modelcompanion_v7.tex)。
SHA256 は `fb32d367e325f081eaeaf77b0c680662c9f58d1e8bc2a45adb0436cbe17c3ad6`。
原稿の著者は Yawara Ishida、Ryosuke Mizuno、Kota Takeuchi、形式化の著者は Yawara Ishida。

[論文対応表](../docs/paper-map.md)は、v7 の60項目・80部分項目について原文の所在、
公開宣言、Lean の証明状態、原稿との照合状態を別々に記録する。
新しい §5 の5項目と §6 の既知の還元を含む57項目・全80部分項目に証明があり、§6 の2つの質問と
Takeuchi予想は `open` として区別する。`open` は未証明定理のstubや公理ではない。

照合は AI agents による原稿・型・主要構成の読解であり、自然言語の意味の機械的認証や
人間による独立査読を意味しない。全項目の登録と全項目の形式化完了は異なる。

## 変更していない数学的規約

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

## 版と検証範囲

[v7 移行記録](v7-migration.md)に旧項目の数学的同一性、移動した番号・行、新規項目、
確認範囲を記録する。新規実装と統合検証は [v7形式化記録](v7-formalization.md)、
未解決問題の検討は [第6節の考察](section-six-analysis.md) にまとめる。
既存の v4 数学的読解は [数学的検証](paper-mathematical-audit.md)、
v4 完成時点の範囲と符号化は [履歴の完成記録](paper-faithful-completion.md)に残す。
その原稿は [archives](../archives/README.md) に保存した。履歴の行・番号・入力hashは
当時の出典を指し、v7 の検証済みという意味に書き換えない。

各時点の機械検証は対応表が指す入力 revision と検証記録に限定される。
過去の検証成功から、変更後のソースの検証成功を推定しない。
Palomar の独立した statement comparison は [登録準備](../docs/palomar.md)に記す。
その選択対象は Theorem 3.3 と Corollary 3.4 であり、論文全項目の自然言語照合とは区別する。
