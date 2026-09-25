# v7 の形式化と検証

> 履歴資料（v7 原稿）。原稿と PDF は [archives](../archives/README.md) に保存。現行版への移行は [v9 移行記録](v9-migration.md) を参照。

2026-09-22。対象原稿は [T3_modelcompanion_v7.tex](../archives/T3_modelcompanion_v7.tex)、
SHA256 `fb32d367e325f081eaeaf77b0c680662c9f58d1e8bc2a45adb0436cbe17c3ad6`。
原稿本文・toolchain・mathlib pin は変更していない。
既存項目の出典照合と archive への移動は [移行記録](v7-migration.md) に記す。

## 数学的範囲

対応表は60項目・80部分項目を追跡する。57項目・全80部分項目に証明があり、
Questions 6.1、6.2、Takeuchi予想の3項目を `open` として区別する。
第6節の未解決問題は証明済みとしない。

| v7 | 実装と照合した内容 |
| --- | --- |
| Remark 4.2 | 既存 `T3.eq_top_of_sup_commutator_eq_top`。指数3の文脈を保持 |
| Example 5.1 / Remark 5.2 | F₃内のA=⟨[x,y],z⟩、正規形によるA≅F₂、中心列、derived subgroupの記述、非strict性、非amalgamation、coproduct比較の非単射性 |
| Lemma 5.3 | 外積のcontractionにより全2n座標をgraded imageへ回収。任意部分群Dの生成濃度に2n下界 |
| Lemma 5.4 | 巡回基底の指定埋込み。第一層の線形汎関数からretractionを作り、直積でamalgamを構成する同値条件 |
| Proposition 5.5 | strict envelopeとnon-amalgamation witness双方の下界。有限巡回基底の位数3・rank1・相互同型、固定自由因子のrank3、両一様上界の不存在 |
| §6, 1519–1525行 | 任意指数nのBurnside群の普遍性と、理論の局所有限性⇔全正有限rankのBurnside群の有限性 |

新しい7モジュールは `ExteriorContraction`、`Free.CommutatorRank`、
`Amalgamation.Cyclic`、`Free.NonStrictExamples`、`Free.UnboundedWitnessRank`、
`Free.Burnside`、`ModelTheory.Burnside`。完全なモジュール名・宣言・行は
[対応表](../docs/paper-map.md) にある。

`Group.rank` は有限生成群に使い、任意部分群に対する下界には既存の
`Group.cardinalRank` を使った。これらの一致は既存のbridgeで証明済み。
部分群の包含を単射準同型で表し、同じ巡回基底からの二つの写像を保持する。
原稿の係数体、下界2n、主要構成を保ち、有限生成等の追加仮定を置いていない。
Burnsideの還元は任意のモデル宇宙に適用でき、空の生成集合も処理する。

実装担当とは別のagentが原稿・Leanの型・主要構成を照合し、数学的な欠落や
弱化を認めなかった。このfidelity reviewはLeanのkernel検証および人間の査読とは別である。
[第6節の考察](section-six-analysis.md) の未Lean化の議論も証明ライブラリとは区別する。

## 検証記録

各新規モジュールの局所buildは警告0で通過した。主要定理の局所公理監査も
`propext`、`Classical.choice`、`Quot.sound` のみである。

`python3 scripts/check.py` の全7段階が終了コード0・警告0で通過した。
検査の開始前後で全入力のhashが不変であることも確認した。

| 検査 | 結果 |
| --- | --- |
| Palomar metadata | 著者・出典・設定整合性を確認 |
| `lake build` | 全ライブラリとSolutionをbuild |
| `mk_all --check` | 新規7モジュールを含むimport網羅性を確認 |
| environment lint | T3全体で通過 |
| text lint | 118ソース、例外なしで通過 |
| axiom audit | 117ソースモジュールの3111宣言、private宣言も含め許可3公理のみ |
| paper map | v7全60項目・80部分項目の所在と全登録宣言をkernel manifestと照合 |

`scripts/verify-comparator.sh` も終了コード0で通過した。
Theorem 3.3 / Corollary 3.4 の指定2宣言の型と定義が一致し、
NanoDaおよびLean標準kernelがSolutionを受理した。
独立specificationのChallengeにのみ、許可された2つのproof holeの警告がある。
Solutionと数学ライブラリはwarning-freeであり、Challengeは数学的import graphの外に置く。
このComparatorの対象は主結果2件で、第5節の網羅監査は上記の全体gateで行う。

入力hash、全宣言manifest、各検査logは
[固定検証成果物](audit-artifacts/2026-09-22/v7-formalization/README.md) に保存した。
検証はローカル作業ツリーのsnapshotを対象とし、commit・公開・提出・登録は行っていない。

新規項目の `code_revision` は7モジュールについて、リポジトリ相対パスをkey、
ファイルSHA256をvalueとする辞書を `json.dumps(hashes, sort_keys=True).encode()`
でJSONにして得たSHA256である。
値は `727f0916bded16958fab4f9916c1c382094e803fb23fcdd36f7847bb7358e7be`。
これはcommit番号ではなく、未commitの証明を特定するsource snapshotである。
旧項目の検証recordは当時のhashと記録を保持し、新しい統合検査はv7全体を対象とする。
