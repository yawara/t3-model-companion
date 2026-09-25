# associated graded の Lie 構造とモデル完全性

> 履歴資料（v4 原稿）。原稿は [archives/T3_modelcompanion_v4.tex](../archives/T3_modelcompanion_v4.tex) に保存。以下の番号・行・検証結果は当時のもの。
> 現行 v9 の対応は [対応表](../docs/paper-map.md) と [v9 移行記録](v9-migration.md) を参照。

2026-09-10。対象は v4 TeX、SHA256
`79745dfa1660a827c51ec3c6b2006ee9d6243cb4702f97a75e5b55357b89f50b`。
[前回の次数商までの境界](infinite-normal-form-and-graded-checkpoint.md) からの進展を記録する。
論文全体の形式化を長期 goal として継続している。

## 群から実際の graded Lie algebra へ

`AssociatedGraded/Bracket.lean` は、群の交換子を二つの中心列商それぞれについて
`QuotientGroup.lift` で降下させる。次数評価と、共役による差が次の中心列に入ることから
双加法性と代表元独立性を得る。この部分は一般群にも成立する。
指数3の場合には標準 `ZMod 3` module上の双線形写像となる。

`AssociatedGraded/Lie.lean` は、既存の実際の次数商の `DirectSum` に bracket を与える。
非零になり得る次数 `(1,1)`, `(2,1)`, `(1,2)` を足し合わせ、群で既に証明した
三重交換子の巡回性と標数3から Jacobi を証明する。
`bracket_lof_mk` は、全正次数でこの Lie bracket が原稿の代表元式と一致することを示す。
次数0は零であり、4以上も零である。canonical range submodules の分解を
`LinearAlgebra/DirectSum.lean` で構成し、標準 `GradedLieAlgebra` を与えた。

誘導写像 `mapLie` は元の quotient maps の DirectSum と同じ関数であり、bracket と
grading、恒等写像と合成を保つ。Proposition 2.24 の二主張も実際の LieHomについて
証明した。三重 bracket の巡回性と反復引数零は全 graded Lie algebra上で成立する。
`AssociatedGraded/Generation.lean` は中心列の subgroup closure induction と直和の帰納法から、
次数1の像の `LieSubalgebra.lieSpan` が全体であることを証明した。
有限生成・rankの仮定はない。これでDefinition 2.18、Lemma 2.19、Definition 2.22、
Proposition 2.24が揃った。

## 外積と自由群

`LinearAlgebra/Wedge.lean` は外積の基本操作と恒等式を与える。
`TruncatedExterior.lean` のcarrierは実際の `Λ¹V × Λ²V × Λ³V` であり、
任意の F₃ ベクトル空間 V を扱う。次数 `(1,2)` の負符号、交代性、Jacobi、内部直和分解、
`GradedLieAlgebra` まで実装した。基底や有限次元を仮定していない。

`Free/Graded.lean` は任意rankの有限支持正規形によってreadoutのkernelを同定する。実際の
`AssociatedGraded.Layer (Free I) n` から、次数1・2・3の有限支持座標への
`LinearEquiv` を構成し、生成元・昇順交換子・三重交換子が単位座標へ写ることを証明した。
`I` に線形順序を置き、有限性・可算性・非空性は仮定しない。

この座標同型のtargetはまだ外積ではない。Proposition 2.29 の σ と Remark 2.30 の
外積 Lie 同型は未完成として対応表に残す。

## 一般モデル理論

`ModelCompleteness.lean` は有限図式を使い、有限個の図式定数を存在変数へ戻す操作と
compactnessの有限被覆を構成した。
これにより `AllEmbeddingsElementary ↔ IsModelComplete` を証明した。
意味論的仮定は既存のcanonical semantic universeを用い、構文的結論を介して
既にある任意universeのelementary preservationに接続する。

`Inductive.lean` は一般Π₂理論について、model companionを仮定した
`M ⊨ T* ↔ IsExistentiallyClosed T M` を証明した。universal theoryには弱めていない。
e.c.モデルからcompanionモデルへの埋込みをTarski–Vaughtで初等埋込みへ上げる。
Fact 2.3 の逆方向、companion/e.c.のuniverse変更bridge、Definition 2.2(6)、
一般bounded-amalgamation criterionは未完成である。

群論のbracket・写像・自由群座標同型とモデル理論の追加証明を、実装担当とは別の担当者も
原稿と照合した。新たな数学的な不一致は見つからなかった。
加法群・scalar actionは既存DFinsupp instanceとの定義的等しさも確認した。
三重bracketの補題のsimp属性が標準simpNFと衝突したため、通常の補題として保持している。

## 検証

`python3 scripts/check.py` の全6 gateが終了値0・警告0で成功した。
25数学モジュール・1,094宣言を公理監査し、private宣言193件を含む。
901宣言の公開性を確認した。依存公理は `propext`、`Classical.choice`、`Quot.sound` のみ。
原稿対応表は50項目中19件が `proved`、5件が `partial`、26件が `planned`。
項目数は作業量や全体の完成率を表すものではない。

最終ソースと対応表のハッシュ、宣言一覧、全gateログを
[固定検証記録](audit-artifacts/2026-09-10/graded-lie/README.md) に保存した。
検査前後と保存時の入力ハッシュは一致する。数学ソース全体のrevisionは
`b9195744eed2e24da93b089b98ccbb16d690fccdcc7807e98b0c092abff93132`。
pin済みcacheによるローカル検証であり、CI実行やmathlib全体のclean rebuildではない。

次はProposition 2.29・Remark 2.30の外積targetへのσとbracket保存、およびLemma 2.31の
一般quotientを実装する。基底・外積計算を用い、任意rankの実際の次数商から接続する。

一般coproduct、同時roots、`15n²`、生成元ベースのsupport、主定理と系は引き続き未完成。
数学的主張の弱化、`sorry`、独自公理による穴埋めは行わない。
