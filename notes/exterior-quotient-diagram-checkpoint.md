# 自由群の外積同型・quotient・有限図式

> 履歴資料（v4 原稿）。原稿は [archives/T3_modelcompanion_v4.tex](../archives/T3_modelcompanion_v4.tex) に保存。以下の番号・行・検証結果は当時のもの。
> 現行 v7 の対応は [対応表](../docs/paper-map.md) と [v7 移行記録](v7-migration.md) を参照。

2026-09-10。対象は v4 TeX、SHA256
`79745dfa1660a827c51ec3c6b2006ee9d6243cb4702f97a75e5b55357b89f50b`。
[前回の graded Lie 構造の境界](graded-lie-checkpoint.md) からの進展を記録する。
論文全体の paper-faithful な形式化を長期 goal として継続している。

## 自由群の実際の次数商から外積へ

`Free/Exterior.lean` は実際の `AssociatedGraded.Layer (Free I) n` の座標同型を
mathlib の外冪基底に接続し、任意の基底 `b : Basis I (ZMod 3) V` に対する
原稿の `sigmaOne`、`sigmaTwo`、`sigmaThree` を構成した。生成元・昇順交換子・
昇順三重交換子の像は原稿の外積そのものである。

`Free/ExteriorBracket.lean` は基底上の交換子計算と双線形性から、次数 `(1,1)` と
`(2,1)` の bracket 保存を証明する。次数1の生成元が対の左・間・右にある場合と
重複する場合を、三重交換子の巡回性・交代性に従って処理する。
生成元・外積計算により、任意rankの次数商と標準mathlib外冪を接続した。

`AssociatedGraded/Truncation.lean` は次数0と4以上が零であることを使い、
実際の `DirectSum` と次数1・2・3の積を同一視する。
`Free/ExteriorLie.lean` はこの同型に `σ₁ × σ₂ × σ₃` を合成し、原稿の直和写像を
`LieEquiv` として構成した。各次数部分空間の像全体の等式も証明している。
混合次数 `(1,2)` の負符号は Example 2.9 と一致する。
実装担当とは別の担当者が、生成元式・符号・次数・rankの仮定を原稿と照合した。

`I` は任意の線形順序付き型であり、有限・可算・非空の仮定はない。
3次数の有限積化はrankの有限性を意味しない。
これで Proposition 2.29 と Remark 2.30 を、座標空間だけでなく外積を値域とする
graded Lie 同型として完成した。

## 一般 quotient、直積、共役幅

`GradedQuotient.lean` は任意の正規部分群Nについて、自然な写像
`grₙ(G) → grₙ(G/N)` の全射性と核が `grₙ(N)` に等しいことを証明する。
核の元の代表元を一段深い中心列の元で補正する原稿の証明に従い、商の同型定理から
Lemma 2.31 のcanonicalな `LinearEquiv` と代表元上の公式を得た。
全次数を扱い、有限生成・strictnessは仮定しない。

`AssociatedGraded/Product.lean` は射影と包含を用いて
`grₙ(G × H) ≃ₗ[F₃] grₙ(G) × grₙ(H)` を構成した。
中心列の直積公式と合わせて Example 2.21(2) を完成した。
同Exampleの可換群・F₂の具体的記述は未完了であり、項目全体は部分完了とする。

`ConjugateWidth.lean` は交換子を圧縮し、原稿の
`Eₐ = {aᵏ[a,g]}` の部分群性・normal closureとの一致を先に証明する。
指数 `k=0,1,2` の場合分けから、任意の元を高々3個の `g⁻¹ * a * g` の積に表す。
全因子はaの正の共役であり、a⁻¹を別の因子として許していない。
自明なaも含め、追加の有限性仮定なしに Proposition 3.1 を完成した。

## 有限言語の図式と e.c. 転送

`ModelTheory/FiniteDiagram.lean` は一般の有限言語について、有限構造の関数表、関係の真偽、
要素の相異性を全て含む単一QF式を作り、
その実現とembeddingの存在が同値であることを証明する。
有限tupleが生成する実際の部分構造を使い、その図式の変数をtupleの項で置き換える。
得られる `finiteGeneratedDiagram` は全QF図式 `tupleQfDiagram` と同じ実現を持つ。
この同値は任意宇宙のtarget構造について成立する。

さらに、e.c.モデルの拡大に埋め込まれた有限構造を、指定tupleを固定して元のモデルへ
戻す補題と、有限共通部分構造を固定する形を証明した。
有限構造自身がTのモデルであるという仮定は不要である。
これは後の Proposition 4.12 の有限構造の転送に使う部品であり、同命題全体の完了ではない。

`ModelTheory/LocallyFinite.lean` は Definition 2.4 を実装し、局所有限性から
全QF図式をその有限部分集合で表せることを導く。
companion/e.c.と同じcanonical semantic universeでモデルを量化しており、
他宇宙へのbridgeは引き続き未実装である。

Definition 2.2(6) の「finite modulo T」をT同値類の集合自体が有限であるという
文字どおりの意味で読むと、その結論はまだ証明していない。
固定した図式の有限連言への圧縮だけで、その図式に含まれる全ての式の同値類数が
有限とは限らない。原稿の強い読みを完成するには、Fact 2.5 の一様上界から
有限個の生成tuple付き有限構造を得て、QF式をその真理値で分類する段階が必要である。
したがって同項目を部分完了、Fact 2.5 を未着手のまま記録する。
原稿の数学的な反例が見つかったという意味ではない。

## 検証と次の境界

`python3 scripts/check.py` の全6 gateが終了値0・警告0で成功した。
34数学モジュール・1,300宣言を公理監査し、private宣言242件を含む。
1,058宣言の公開性を確認した。依存公理は
`propext`、`Classical.choice`、`Quot.sound` のみ。
検査前後と保存時の入力ハッシュは一致する。
全gateログ・宣言一覧・入力ハッシュは
[固定検証記録](audit-artifacts/2026-09-10/exterior-quotient-diagram/README.md) に保存した。
pin済みcacheによるローカル検証であり、CI実行やmathlib全体のclean rebuildではない。
数学ソースのrevisionは
`e3de61dd26f9d1aae8103af7978dd3efdcb8656534e580c143c83938a8ec654a`。
論文対応表は50項目中24件が `proved`、4件が `partial`、22件が `planned`。
この項目数は全体の作業量や完成率を表さない。

実装計画の段階3で設定した自由群の外積同型と一般quotientの境界に到達した。
次は Proposition 4.1 のpresentation、Lemma 4.2 のgraded normal closureを構成し、
Proposition 4.3 のη₁–η₃と自然性へ進む。

- Prop 4.1 の公開定理は、与えられた `Layer G 1` の基底とその代表元からの写像を扱う。
  群の生成性の証明を、associated gradedのLie生成性だけで済ませない。
- Lemma 4.2 の群としての等式は、一般の指数3群について normal closure を計算して得る。
  その後の次数2・3の等式は実際の `subgroupImage` とbracket部分空間上で証明する。
- 独立に進められる次の構成は Lemma 4.8 の同時triple rootsである。
  `F_(3n)` の独立な三重交換子を使って一括商の核を計算する。
  今回の直積と次数3座標が利用できる。

上記は次回の実装計画であり、今回の検証済みコードには数えない。

生成元ベースのsupport、同時roots、`15n²`、一般criterion、主定理と系は未完成。
原稿の構成に従って証明し、`sorry`・独自公理・強い追加仮定は使わない。
