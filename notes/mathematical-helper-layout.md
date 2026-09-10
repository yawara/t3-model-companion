# 数学分野と論文中の構成に沿った補助補題の配置

2026-09-10。`ForMathlib` の5モジュールを、[配置方針](lean-architecture.md)に沿って整理した。
直和・部分群・線形写像の商・テンソル積の補題は数学分野別の基礎モジュールに置き、
固定濃度部分集合の直和分解は `ExteriorTensor` の準備部分に統合した。
線形写像の商の補題は使用先の `Coproduct.GradedEquiv` が直接 import する。
宣言の名前・型・証明・既存 namespace・Paper-ID・出典・著作権表示を保持した。

移動前の[論文全体の検証・fidelity 記録](paper-faithful-completion.md)は保存している。
その数学ソース revision は `0895205ed3ac7498330f87694e712d6e89edda228a294a628eaa1885557d3de5`。
今回の変更では数学的主張を変更せず、既存の fidelity 照合を引き継ぐ。
独立レビューでも、移した宣言ブロックと既存 `ExteriorTensor` 本体の文字列一致、
変数スコープ、出典を確認した。109モジュールの import グラフに循環・欠落・旧 import はない。

今回の数学ソース revision は
`92a68de03c4ad4fe992d652a08f33cb9a8d9c3027ce5650dd7ea40d7dbbfbd2e`。
これは `T3.lean` と `T3/**/*.lean` の path-to-SHA256 辞書を `sort_keys=True` で JSON 化した
ものの SHA256。論文対応表の全 verification はこの入力と本記録を指す。
原稿、toolchain、manifest と、過去の検証成果物は変更していない。

## 検証

`python3 scripts/check.py` の全6段階（build、import 集約、environment lint、text lint、
公理監査、論文対応検査）が終了コード0・警告0で通過した。
全109モジュール・2,973宣言を監査し、公理依存は `propext`、`Classical.choice`、
`Quot.sound` のみ。論文対応表は全50項目・75部分項目が `proved` / `proof_checked`。
検査中の入力不変性と、保存時の全入力ハッシュの一致を確認した。

移動前後の kernel 宣言一覧を比較し、公開名2,394件の集合、export 状態、公理依存集合が
一致することを確認した。公開宣言の名前空間を保持し、import パスを新配置へ変更した。
独立したソース比較では、移した宣言の変数・型・証明本体がそのままであることも確認した。
これは配置変更の再検証であり、自然言語の原稿全体を新たに査読した記録ではない。

[保存成果物](audit-artifacts/2026-09-10/mathematical-helper-layout/README.md)に
入力ハッシュ、全宣言一覧、6段階のログ、公開名の比較結果を保存した。
pin 済みキャッシュを用いたローカル検証であり、mathlib 自体の clean build や CI 実行を
意味しない。今回の検査後、数学ソースと対応表は変更していない。

> 公開履歴の整理に伴い、非公開の作業場所・内部識別子を省略した。数学的記述と当時の検証結果は保持しており、ここに記す検証は当時の対象に限る。
