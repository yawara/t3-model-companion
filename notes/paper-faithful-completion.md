# v4 論文全体の paper-faithful 形式化

> 履歴資料（v4 原稿）。原稿は [archives/T3_modelcompanion_v4.tex](../archives/T3_modelcompanion_v4.tex) に保存。以下の番号・行・検証結果は当時のもの。
> 現行 v9 の対応は [対応表](../docs/paper-map.md) と [v9 移行記録](v9-migration.md) を参照。

2026-09-10。対象原稿の全数学項目の形式化・fidelity 照合を完了した。
110モジュールの最終全体検査が終了コード0・警告0で通過した。

## 最終検証結果

`python3 scripts/check.py` の build、import 集約、environment lint、text lint、公理監査、
論文対応検査の全6段階が通過した。検査中の入力不変性と保存時の live SHA256 一致も確認した。
2,973宣言、private-name 579、public-name 2,394を監査し、後者は全て exported。
exported 全体2,411には生成された private-name の補題17個も含まれる。
許可および実際の公理は `propext`、`Classical.choice`、`Quot.sound` のみ。
`sorry`、`admit`、独自公理、lint 例外を使わず、全50項目・75部分項目が
`proved` / `proof_checked`。数学的未完項目は残っていない。

[最終保存成果物](audit-artifacts/2026-09-10/paper-completion/README.md) に全入力・全宣言・
6段階のログと独立レビューの記録を固定した。pin 済みキャッシュを用いたローカル検証であり、
mathlib 自体の clean build や CI 実行を意味しない。

## 対象と主張

対象はリポジトリ直下の `T3_modelcompanion_v4.tex`。
原稿 SHA256 は `79745dfa1660a827c51ec3c6b2006ee9d6243cb4702f97a75e5b55357b89f50b`。
本文を変更せず、47個の番号付き項目、Proposition A、2個の数学的本文項目を形式化した。
対応表は50項目・75部分項目で、例・remark・記法も含む。
§1/§5/§6 の編集用 placeholder は数学的主張を含まないため定理として数えない。

主定理は `T3.exists_bounded_nonamalgamation_witness`、系は `T3.has_model_companion`。
前者の上界は原稿の

```
t(n)  = n + n.choose 2 + n.choose 3
f₀(n) = 15 * n^2
f(m)  = f₀((3*m+4)*t(m)+1)
```

そのものである。それぞれ自由群の正規形、strict envelope、主定理のモジュールに置いた。
model companion の存在に、未供給の上界や構造定理を追加仮定として残していない。

## 原稿への対応

数学的正しさの初期監査で省略されていた論証を展開した。原稿の同時 quotient、
自由表示、非斉次の関係、canonical な graded 写像と符号、任意 rank、有限 support、
欠損商の基底を保った。

原稿の数学と Lean の符号化の対応は次のとおり。

- 群の指数は3を割る条件で、自明群を含む。中心列の添字のずれは定義と bridge で管理する。
- `d(G)` は任意群では `Group.cardinalRank`。有限生成時には `Group.rank` と一致する。
- associated graded は実際の群の商から構成した vector space と Lie algebra であり、
  部分群の graded image は ambient filtration を使う。正次数 grading の次数0は零。
- 有限図式の一つの有限連言と、QF 式の理論同値類の有限代表集合を両方証明している。
- 補助的な η₁ の全単射性は、同じ canonical map を普遍性と retraction で直接示す。
  η₂/η₃ と主定理の主要経路は原稿の presentation・block 計算・商・support を保つ。
- canonical universe の元の意味論的定義には、任意宇宙でのモデル埋込み、e.c. 性、
  局所有限性、ordinary amalgamation、有界障害の双方向 bridge を付けた。
  `Small M` や入力モデルの基数制限は残さない。

Lemma 4.7/4.9 の欠損生成元は実際の graded kernel の基底から供給する。
Proposition 4.12 は二段階の同時 strictification と `D₂ ∐ F₂`、全 C を固定する有限図式で
`15n²` と内部中心列の一致を得る。Cが自明な場合は C 自体を返し、n=0も覆う。
Theorem 3.3 は原稿の log/rank の連鎖、`3(m+1)n` の support、内部 normal closure、
strict coproduct、左右両方の非 amalgamation 証人を使う。

最後に統合した Remark 4.10 は、F₄ の4つの三重交換子を共有する実際の `(G×F₄)/L` と、
同じ商の D の strictness を証明し、追加生成元数を4にする。
最後の一文も F₃ の3つの pair を共有する coproduct quotient で実装し、
derived strictification の追加生成元数を3にする。指定された群の元に独立性・非零性を
課さない。原稿が述べていない任意 n の最適上界は主張しない。

一般 Fact 2.6 は、任意宇宙での ordinary amalgam と有界障害の両方向を持つ。
必要方向の上界 `k+|A|` と、有限 marked 障害から extension sentences を作る十分方向を
保つ。有限構造自身の T-model 性や非空性は追加しない。

## 検証と照合の区別

Lean の kernel 検証・全数学宣言の公理監査・lint と、自然言語の原稿との fidelity 照合は
別の検査である。対応表の自動検査は source locator と公開宣言の対応を検査するもので、
自然言語の意味まで自動認証するものではない。

各段階で原稿・公開型・主要証明経路を読み合わせ、重要な構成に独立レビューを実施した。
最終 sweep は原稿の全項目、型、仮定、実際の証明の供給元を確認した。
全既存 proof body をこの最終 sweep で新たに逐語再査読したという意味ではない。
そこで残っていた Remark 4.10 と一般 Fact 2.6 の宇宙接続を今回統合し、公開型と証明を
改めて照合した。原稿の数学的主張の修正、追加仮定、未供給の producer は必要なかった。

数学ソース revision は
`0895205ed3ac7498330f87694e712d6e89edda228a294a628eaa1885557d3de5`。
これは `T3.lean` と `T3/**/*.lean` の path-to-SHA256 辞書を `sort_keys=True` で JSON 化した
ものの SHA256。全項目の verification はこの最終入力を指す。
過去の段階の audit snapshots は変更せずに保存している。

Lean 4.32.2、mathlib `905b95818eb32af7874a58b427f50c1711a5e96c` に固定。
