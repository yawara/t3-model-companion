# v9 §2–3 と Lean の照合

確認日: 2026-09-25。受領した `main_v9.tex` の SHA-256 は
`d48f10716bcc7963b654c6fe27013ac75eaa9cbdf6593683a0efc513dd062952`。
この記録の TeX 行番号はこの受領版を指す。ユーザーの指示に従い、受領した TeX 自体を
正本として保存する。`T3_modelcompanion_v9.tex` は受領版と byte-identical な内容へ復元し、
以下の文章上の指摘は提案としてのみ記録する。正本の所在は `docs/paper-map.toml` に従う。

## 結論と確認範囲

§2–3 の主張・仮定・定数・量化順序と、以下の Lean の公開宣言および主要な証明経路を
照合した。数学的な主張の相違や追加仮定による穴埋めは見つからなかった。
`f₀(n) = 15n²`、`t(m) = m + choose m 2 + choose m 3`、
`f(m) = f₀((3m+4)t(m)+1)` は一致する。

受領時点では、`\section{Preliminaries}` から `\section{Structural analysis}` の直前までが
v8 と byte-identical であることも確認した。ただし、この同一性だけを fidelity 判定の根拠には
せず、現在の Lean 宣言と主要な証明を読み直した。今回の手作業の照合と、統合時に行う
`scripts/check.py` の kernel・axiom・lint 検査は別の検証である。この担当レビューでは
ビルドや全体の axiom audit を実行していない。

## モデル理論の定義と一般判定

| 受領 v9 の所在 | 確認した公開境界 | 照合内容 |
|---|---|---|
| Definition 2.2(1–4), 272–277行 | `ModelCompanion.lean`: `ModelsEmbedInto`, `IsCompanion`, `IsModelComplete`, `IsModelCompanionOf`, `IsExistentiallyClosed`; `ExistentialClosedness.lean`: `IsExistentiallyClosedAt` | companion は両方向の embedding。原稿の inclusion は像との同型で実現する。model completeness は各式の existential rewriting という原稿の定義であり、意味論的条件だけへの置換ではない。e.c. のパラメータと existential variables は有限タプルで、拡大モデルへの embedding に沿って反映する。 |
| Definition 2.2(5), 278行 | `Inductive.lean`: `IsPiTwo` | 同じモデル類を定める `∀∃` 文集合の存在。`T` 自身の構文を不必要に固定しない。 |
| Definition 2.2(6), 279–286行 | `FiniteDiagram.lean`: `finiteGeneratedDiagram`, `realize_finiteGeneratedDiagram_iff_tupleQfDiagram`; `UniformLocalFiniteness.lean`: `exists_finite_qf_representatives`, `exists_finite_tupleQfDiagram_representatives` | 有限タプルの生成部分構造の有限性から、一つの有限図式を構成するだけでなく、modulo `T` の有限代表族も得ている。有限言語の仮定を保持する。 |
| Fact 2.3, 289–295行 | `ModelCompanionCriterion.lean`: `isModelCompanionOf_iff_models_iff_isExistentiallyClosed`; `ExistentialClosedness.lean`: `models_iff_isExistentiallyClosedAt` | `Π₂` 仮定で、companion のモデル類と e.c. モデル類の一致を両方向に証明。逆方向は e.c. extension と Robinson test を用い、有限言語・局所有限性・普遍性を追加しない。 |
| Definition 2.4 / Fact 2.5, 297–306行 | `LocallyFinite.lean`: `IsLocallyFinite`; `UniformLocalFiniteness.lean`: `exists_finite_qfType_cover`, `exists_card_closure_le_of_isLocallyFinite` | 局所有限性はモデル内の有限集合の生成部分構造に課す。compactness で固定長タプルの有限型被覆を作り、全モデル・全生成集合に共通の濃度上界を得る。生成部分構造そのものが `T` のモデルであるとは仮定しない。 |
| Fact 2.6, 308–323行、証明325–357行 | `BoundedAmalgamation.lean`: `FiniteInclusion`, `GeneratedByAtMost`, `BoundedAmalgamationObstructions`; `BoundedAmalgamationCriterion.lean`: `hasModelCompanion_iff_boundedAmalgamationObstructions` | 任意の有限 inclusion `A ↪ B` に対し一つの `n` を選び、その後にすべての e.c. `M` と base marking を量化する。上界は base 以外の追加生成元数ではなく、`C` の総生成元数である。 |

Fact 2.6 の主要構成を次のように確認した。

- `FiniteInclusion` は `B` があるモデルに埋め込めることだけを要求する。一般の `Π₂` 理論で
  `A` や `B` をモデルにしてしまう変更はない。有限構造は空の場合も許す。
- 必要方向は negated extension formula を existential formula に書き換え、その有限 witness
  と base の全要素で `C` を生成する。得られる上界は `k + |A|` で、`M` に依存しない。
- 十分方向では `FiniteObstructions.lean` の `FiniteMarkedStructure` が有限 carrier 上の
  構造と base marking の両方を記録する。`exists_finite_bad_marked_cover` の同型は base の全要素を
  固定する。単に抽象群の同型型を有限個にして marking を落とすことはない。
- `extensionTheory` のモデルから e.c. 性を得る際には、ambient model の中で
  `A = closure(parameters)` と `B = closure(witnesses ∪ A)` を作る。`C` と `B` の禁止 amalgam
  が ambient extension に埋め込まれるという矛盾で、原稿と同じ extension axiom を適用する。
- canonical semantic universe の定義だけで止まっていない。
  `ModelEmbeddings.lean`, `ExistentialClosedness.lean`,
  `LocallyFinite/Universes.lean`, `UniformLocalFiniteness/Universes.lean`,
  `Amalgamation/Universes.lean`, `BoundedAmalgamation/Universes.lean` に任意宇宙への bridge がある。
  特に `IsExistentiallyClosedAt.reflects_of_model` は source 全体を含む Skolem hull を取り、
  target universe の制限を除く。`hasModelCompanion_iff_boundedAmalgamationObstructionsAt` は
  より大きい model universe での判定も与える。可算性の追加仮定はない。

## 代数的準備

| 受領 v9 の所在 | 確認した宣言・モジュール | 照合内容 |
|---|---|---|
| §2 冒頭 / Notation 2.1, 227–266行 | `Basic.lean`, `Notation.lean`, `GeneratorRank/Cardinal.lean`, `Free/Basic.lean`, `Coproduct/Basic.lean` | exponent は `∀ x, x^3=1`、自明群を含む。交換子は `aba⁻¹b⁻¹`、右共役は `b⁻¹ab`。自然数の `Group.rank` を使う定理には有限生成を明示し、任意 rank の記法には `cardinalRank` と比較定理がある。 |
| Definition 2.7 / Remark 2.8, 361–381行 | `LinearAlgebra/GradedLie.lean`: `IsPositive`, `lieSpan_eq_top_iff_map₂_eq_grade` | 自然数次数の 0 成分を 0 として、原稿の正次数 grading を表現する。degree-one generation と `span [Lᵢ,L₁] = Lᵢ₊₁` の両方向を direct-sum decomposition と反復 bracket で証明する。 |
| Example 2.9, 383–400行 | `TruncatedExterior.lean`: Lie instances, `ofOne_lie_ofOne`, `ofTwo_lie_ofOne`, `ofOne_lie_ofTwo` | `(1,1)` と `(2,1)` の符号は正、`(1,2)` は負。全次数 4 以上は 0。Jacobi の計算で characteristic 3 を実際に使用する。三成分の積表示は次数の有限性だけを利用し、`V` の有限次元性を仮定しない。 |
| Definition 2.10 / Proposition 2.11, 402–414行 | `BlockDecomposition.lean`: `IsBlockHomogeneous`, `isBlockHomogeneous_iff_iSup_eq`, `blockIntersections_independent`, `quotientEquiv_mk_apply` | homogeneous predicate と原稿の直和表示の同値を証明。商同型は代表元を各成分の商類へ送る実際の canonical map。block index の有限性は不要。 |
| Definitions 2.12, 2.23, 2.25 / Remark 2.13 / Facts 2.14 / Lemma 2.26, 420–443, 554–562, 597–615行 | `CentralSeries.lean`: `mem_upperCentralSeries_iff_forall_fin`, `IsStrict`, `CentralSeriesCoincide`, `centralSeries_inclusions`, `isStrict_of_centralSeriesCoincide` | mathlib の lower-central index 0 が原稿の `γ₁` に対応する。strictness は内部 `γ₂,γ₃` と ambient intersection の等式。UL coincidence から任意の exponent-three ambient 内の strictness を得る包含列を保持する。 |
| Fact 2.15, 449–465行 | `Identities.lean`, `Free/Examples.lean` | 左右の積公式、三重交換子の cyclic/swap、逆元公式、principal normal closure の可換性と class ≤ 3 に対応する型を確認。集合の積に対する二包含は任意の sets に対して証明されており、部分群だけに狭めていない。`Z₂` が一般には非可換という部分には実際の free-rank-two 例がある。 |
| Fact 2.16 / Lemma 2.17, 468–480行 | `Coproduct/Basic.lean`: `sumEquivCoproduct`, `fst`, `snd`, `inl_injective`, `inr_injective` | free generating sets の disjoint union は和型で表現。因子の単射性は他方を 1 に送る retraction による。 |
| Definition 2.18 / Lemma 2.19 / Notation 2.20, 485–531行 | `AssociatedGraded.lean`, `AssociatedGraded/Bracket.lean`, `/Lie.lean`, `/Generation.lean` | 実際の consecutive lower-central quotients とその direct sum を使う。代表元の bracket を商へ降ろし、F₃-linear 化する。degree one からの生成は lower-central closure induction で、有限生成の仮定はない。 |
| Example 2.21, 533–539行 | `AssociatedGradedExamples.lean`: `abelianLieEquiv`, `firstLayerBasis`, `secondLayerBasis`, `mem_term_two_iff`, `term_three_eq_bot`; `AssociatedGraded/Product.lean`: `term_prod`, `layerProdEquiv` | 可換群の bracket が 0 で degree one のみとなること、直積の各層の自然同型、`F₂` の derived subgroup が named commutator の三つの冪であることを確認した。 |
| Definition 2.22 / Proposition 2.24, 543–552, 564–595行 | `AssociatedGraded.lean`: `mapLayer`, `map_injective_iff_isStrict`; `/Lie.lean`: `mapLie`, `injective_of_mapLie_injective`, `mapLie_injective_iff_isStrict` | 誘導写像は初期成分上で `a ↦ f(a)`。graded injection が group injection を含意し、group injection を仮定したとき strict image と同値になる。|
| Fact 2.27 / Remark 2.28, 619–639行 | `Free/NormalForm.lean`: `freeOrderExponent`, `natCard_eq_pow_freeOrderExponent`, `normalWord`, `existsUnique_normalWord`; `/FiniteSupport.lean`: `exists_finset_map`; `/InfiniteNormalForm.lean`: `existsUnique_normalWordFinsupp` | 位数は正確に `3^t(r)`。有限版は昇順の generator block、pair block、triple block の実際の積。無限版は三つの `Finsupp` 係数族の存在一意性。有限の支持への還元から得ており、無限個の generator を有限 rank として扱わない。 |
| Proposition 2.29 / Remark 2.30, 644–696行 | `Free/Exterior.lean`: `sigmaOne`, `sigmaTwo`, `sigmaThree` と generator 上の公式; `/ExteriorLie.lean`: `exteriorLieEquiv`, `exteriorLieEquiv_grade` | actual graded layers の昇順 pair/triple basis から exterior basis に移す。bilinearity で bracket 保存を証明し、graded subspace の像の等式もある。任意の線形順序付き生成集合とその基底で成立し、有限・可算・非空を仮定しない。 |
| Lemma 2.31, 717–733行 | `GradedQuotient.lean`: `mapLayer_quotient_surjective`, `mapLayer_quotient_ker`, `quotientLayerEquiv`, `quotientLayerEquiv_mk` | 正規部分群 `N` に対して natural quotient map の kernel が ambient graded image となり、商同型を得る。`N` の strictness や有限生成を追加しない。 |

## 主結果と依存関係

Proposition 3.1（746–757行）は `ConjugateWidth.lean` の
`principalNormalForm_eq_normalClosure` と `normalClosure_eq_conjList` に対応する。
`Eₐ = {aᵏ[a,g]}` の subgroup/normal-closure 計算の後、`k = 0,1,2` を場合分けして
それぞれ高々 3 個の正の共役 `g⁻¹ag` にする。`a⁻¹` の共役を別の許容因子として
追加してはいない。

Lemma 3.2（761–786行）は `Support.lean` の `exists_bounded_support_set` と
`exists_bounded_support_rank` に対応する。`Support/Collection.lean` と
`Support/Conjugator.lean` の class-two quotient での collection を通じ、各共役を
高々 `m+1` 個の `G` の元で表現し、principal width 3 と有限 relation family の和集合で
`3(m+1)n` を得る。結論は実際の `C ≤ G` と `H₀ = ⟨C,B,Δ⟩` 内部の normal closure への所属である。
ambient normal closure への所属だけで済ませていない。`Δ.encard ≤ n` から有限性を回復し、
`n = 0` や自明群を排除していない。

Proposition A（790–792行）の公開境界は `StrictEnvelope.lean` の
`exists_bounded_strict_envelope`。`exists_strict_envelope` は `C ≤ D ≤ M` と
`rank D ≤ strictEnvelopeBound n`、`IsStrict D` を返し、subsingleton の枝も処理する。
ここでは §4 の strict-envelope producer の呼出しと e.c. transfer 境界を確認した。
その producer 内部の roots と `15n²` の算術計算は §4 担当レビューの範囲である。

Theorem 3.3（795–833行）は `Main/BoundedWitness.lean` の
`exists_bounded_nonamalgamation_witness` と `exists_uniform_nonamalgamation_bound`。
principal route を始点から終点まで確認した。

1. `Amalgamation.lean` の coproduct quotient で普通の amalgamation を表現する。
   強い amalgamation の intersection 条件は課さない。`exists_witness_of_generating_family` は
   base generators の relators だけを使い、左右どちらの factor の kernel witness も返す。
2. `GeneratorRank/Cardinality.lean` の `rank_le_freeOrderExponent_of_injective` が原稿どおり
   `rank A ≤ log₃ |A| ≤ log₃ |B| ≤ t(m)` を証明する。`A` の有限性を Lean の `[Group.FG A]` で
   表す箇所は exponent three による局所有限性で同値になり、主張を弱めていない。
3. support の `Y`、base generating set、左 witness の singleton を合併し、総数を
   `3(m+1)n+n+1 ≤ (3m+4)t(m)+1` で評価する。右 factor の witness では singleton を空集合にする。
4. `exists_strict_envelope` から `D` を得る。`Coproduct.map_injective_of_strict` で
   `D ∐ B → M ∐ B` の単射性を取り、`Support/Transport.lean` の
   `mem_normalClosure_of_mem_normalClosureIn` と relator inverse-image の等式で、証明書を
   小さい coproduct に引き戻す。これは単なる上向き transport ではない。
5. 左右の kernel witness をそれぞれ非自明のまま残して `D` と `B` の非 amalgamation を得る。
   `witnessBound` は `m` のみに依存する。`M`, `A`, `B` の追加の濃度制限はない。

Corollary 3.4（835–838行）は `Main/ModelCompanion.lean` の
`exponentThreeTheory_boundedAmalgamationObstructions` と `has_model_companion`。
有限構造に group operations を回復する際には `T₃` の普遍性を明示的に使用する。
base を e.c. model 内の像に取り直し、ordinary group amalgam と first-order amalgam の bridge、
総生成元数の substructure への bridge を通して Fact 2.6 に適用する。
`ExponentThree.lean` は有限言語、`Π₂` 性、有限 rank free group による局所有限性を供給する。

## 原稿の明確化案（未適用）

`notes/v8-paper-review-2026-09-24.md` の §4 に残っていた軽微な指摘を、受領 v9 と再照合した。
レビュー中に一度行った次の文章上の変更は、TeX 自体を変更しないというユーザーの指示に
従って取り消した。以下は未適用の提案であり、正本の修正済み事項ではない。
いずれも数学的な仮定・上界・主要構成の変更を提案するものではない。

- 271行: 未対応の `T,T'` の導入を、言語 `L` とこの subsection 内の理論の一般規約に置換する案。
- 278行: `T ≡ T'` を「同じモデルをもつ」と明記する案。
- 356行: 崩れた `B' ⊂ M ⊨ θ` を `B' ⊂ M` と `M ⊨ θ` に分離する案。
- 638行: 無限 rank の正規形について、有限支持への還元、有限生成集合の inclusion の retraction、
  二つの表現の共通有限支持を用いた一意性を明記する案。
- 795行: Theorem 3.3 の optional title を `Bounded-witness theorem` に変更し、
  序論の Main Theorem（Corollary 3.4）との重複を解消する案。
- 821–822行: 生成元数の文章に `at most` を加え、不等式であることを明記する案。
- 835行: Corollary 3.4 の直前に有限言語・普遍性からの `Π₂` 性・局所有限性を補い、
  Fact 2.6 の仮定を明示する案。

Fact 2.3 の原典 citation と、Fact 2.6 を既知の fact と呼ぶか命題と呼ぶかは、今回の Lean との
一致とは別の編集上の判断である。このレビューでは新しい帰属を推測して追加していない。

## 検証の境界

この記録は §2–3 の全 numbered item と必要な公開 bridge の型、および主結果の主要構成の
source-fidelity review である。3,000 以上ある全補助宣言の証明を一行ずつ独立に再証明した記録、
引用文献の全証明の再監査、§4–5 の担当レビュー、公開・投稿・登録の完了を意味しない。
今回、Lean の数学的定義や theorem body に変更が必要な不一致は見つからなかった。
docstring の版・source locator と対応表の更新、および実際の統合検査結果は移行担当の記録に従う。
