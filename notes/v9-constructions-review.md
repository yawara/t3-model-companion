# v9 §4–5 と Lean の構成照合

2026-09-25。対象は受領した `main_v9.tex` と、その内容を変更せず採用する
`T3_modelcompanion_v9.tex`。受領ファイルの SHA256 は
`d48f10716bcc7963b654c6fe27013ac75eaa9cbdf6593683a0efc513dd062952`。
以下の TeX 行番号は**受領版**の所在である。
ラベルのない項目は表示番号と内容で同定する。

## 結論と検査境界

§4 の 13 項目と §5 の 5 項目について、主張、仮定、定数、主な構成、
主要な中間命題を現在の Lean ソースに再照合した。
この範囲で数学的主張・Lean の型・定数を変更する必要は見つからなかった。
全群を有限群に制限する、任意 rank を有限 rank に制限する、
`F₂` を `F₃` へ置き換える、生成元数を位数で置き換える、といった不一致はない。

受領 v9 の §4–5 は v8 の同範囲と同一であり、前方の編集により行番号が
10 行移動しただけである。これは `diff -u` による現在のファイル同士の比較で
確認した。その上で、下記の宣言と証明経路を実際に読み直した。
既存の `proof_checked` 表示や過去のビルド成功だけを根拠にした判定ではない。

この記録は静的な原稿照合の記録であり、今回の kernel、axiom audit、lint、
Palomar 検査の実行記録ではない。全体の検査は移行作業の統合段階で実施する。
低層の全補助証明を一行ずつ再レビューしたという主張もしない。

## 項目ごとの照合

以下の Lean パスはリポジトリルートからの相対パス。

| 受領 v9 の項目と所在 | 現在の主要宣言・証明境界 | 照合内容 |
| --- | --- | --- |
| Proposition 4.1、852–892、`proposition:lift` | `T3/GroupTheory/Presentation.lean` の `T3.Free.presentation_of_basis`、`liftLayerOneEquiv`、`lift_ker_le_commutator_of_basis` | 任意の指定された abelianization の基底と代表元から、実際の `Free.lift` の全射性と核の derived への包含を得る。基底に有限性・可算性を仮定しない。 |
| Remark 4.2、894–896、`remark:G=H` | `T3/GroupTheory/Generation.lean` の `T3.eq_top_of_sup_commutator_eq_top` | §4 の指数 3 群という文脈で `H ⊔ commutator G = ⊤` から `H = ⊤`。原稿の二段階の交換子包含を用いる。 |
| Lemma 4.3、898–936、`lemma:gr of normal closure` | `T3/GroupTheory/GradedNormalClosure.lean` の `normalClosure_eq_sup_commutator`、`mem_normalClosure_iff_mul_commutator`、`normalClosure_inf_term_three`、`subgroupImage_normalClosure_two`、`subgroupImage_normalClosure_three` | `K ≤ γ₂(G)` のみで実際の積 `K[K,G]` を経る。`K` の正規性を加えず、非斉次な関係式を次数別に勝手に分離しない。 |
| Proposition 4.4、939–1022、`proposition:gr of free product` | `T3/GroupTheory/Coproduct/{Graded,GradedEquiv,Presentation,Relations,QuotientMaps,BlockBracket}.lean` | 基底 lift、自由群の外冪分解、関係像の四成分、商の核輸送から、canonical な `layerTwoMap`、`layerThreeMap` の全単射性を得る。`block`、`bracket_block_le` は全次数について block の bracket 包含を述べる。 |
| Lemma 4.5、1042–1055、`lemma:free-product-amalgam` | `T3/GroupTheory/Coproduct/Strict.lean` の `mapLayer_map_injective`、`map_injective_of_strict` | 同じ η の自然性と体上の tensor 積の単射性を使い、graded の単射性から群の単射性へ戻る。両因子の有限生成性を追加しない。 |
| Lemma 4.6、1058–1096、`lemma:coincidence of central series` | `T3/GroupTheory/Coproduct/{CentralSeries,FreeTwoSeparation}.lean` の `freeTwo_stabilization`、`centralSeriesCoincide_freeTwo` | 原稿どおり非自明な `G` と `Free (Fin 2)`。degree 1 と degree 2 の二つの分離論証から中心列一致を得る。`Nontrivial G` は原稿の `1 ≠ G` に対応する。 |
| Lemma 4.7、1106–1169、`lemma:basic commutator root` | `T3/GroupTheory/Roots/Commutator.lean` の `Extension`、`coefficients_eq_zero`、`centralWord_eq_one`、`baseMap_injective` | `G ∐ F₂ₙ` を指定された root 関係の正規閉包で割る構成。degree 2 で各係数を消し、degree 3 の `(1,2)` block で `sᵢ = 0` を得て base の核を消す、原稿の三 claim に一致する。 |
| Lemma 4.8、1172–1204、`lemma:commutator root` | `T3/GroupTheory/Roots/{DefectBasis,DerivedStrictification}.lean` の `exists_derived_defect_generators`、`exists_derived_strictification` | 第 1 層の写像の核の基底を lift。追加生成元は高々 `2m`、総数は高々 `3m`。同時 root 商を使い、`D ∩ γ₂(H) = γ₂(D)` を得る。 |
| Lemma 4.9、1206–1225、`lemma:triple commutator root` | `T3/GroupTheory/Roots/Triple.lean` の `Extension`、`eq_one_of_inl_mem_kernel`、`baseMap_injective`、`baseMap_root` | ここは coproduct ではなく `G × F₃ₙ` の中心的関係商。仮定は各 `gᵢ ∈ Z(G)` であり、`gᵢ ∈ γ₃(G)` を追加しない。自由 triple の係数で base の単射性を証明する。 |
| Lemma 4.10、1229–1271、`lemma:number of generators for triple commutator roots` | `T3/GroupTheory/Roots/{DefectBasis,LowerCentralStrictification}.lean` の `exists_lowerCentral_defect_generators`、`isStrict_enlargedSubgroup`、`exists_strict_extension` | 既に成立する第 1 の strictness を使い、第 2 層の核の基底を選ぶ。追加生成元は `3 * n.choose 2`、すなわち `3n(n−1)/2`。二つの交わり等式を同じ直積商の中で証明する。 |
| Remark 4.11、1273–1278 | `T3/GroupTheory/Roots/{SharedTriple,SharedLowerCentralStrictification,SharedCommutator,SharedDerivedStrictification}.lean` | 四つの独立な triple を `F₄` で共有し、四つの defect を四生成元で除く結果を持つ。commutator 版も三つの pair を `F₃` で共有して実装。主定理の `15n²` の計算には、この改善を混ぜていない。 |
| Proposition 4.12、1281–1301、`proposition:structure of e.c. model` | `T3/ModelTheory/ExistentiallyClosedGroups.lean` の `exists_group_embedding`、`nontrivial`、`centralSeriesCoincide`、`commutator_eq_setOf_commutator`、`lowerCentralSeries_two_eq_setOf_triple_commutator` | root 拡大と `M ∐ F₂` の分離を有限図式で元の `M` に戻す。すべてのパラメータを固定する。`M` の非自明性は e.c. から証明し、外から仮定しない。 |
| Proposition 4.13、1308–1347、`proposition:bdd LCS` | `T3/ModelTheory/StrictEnvelope.lean` の `strictEnvelopeBound`、`three_stage_rank_le_strictEnvelopeBound`、`exists_centralSeries_extension`、`exists_strict_envelope` | `D₁`、`D₂`、`D₂ ∐ F₂` と原稿どおりに構成。有限図式の移送は `C` の全要素を固定し、実際の `C ≤ D ≤ M` を与える。中心列一致と ambient での strictness の両方を結論に含む。 |
| Example 5.1、1361–1374 | `T3/GroupTheory/Free/NonStrictExamples.lean` の `nonStrictLift_injective`、`nonStrictSubgroup_mem_commutator_iff`、`nonStrictSubgroup_not_isStrict`、`nonStrictWitness_ne_one`、`nonStrict_not_amalgamable` | `A = ⟨[x,y],z⟩ ≅ B(2,3)`、非 strictness、指定 triple による非 amalgamation、coproduct 比較の非単射性を同じ具体的部分群で証明する。 |
| Remark 5.2、1376–1382 | 同ファイルの `nonStrict_coproduct_map_not_injective` | strictness を除いた Lemma 4.5 の反例である。Theorem 3.3 の証人輸送と区別する。 |
| Lemma 5.3、1388–1423、`lemma:D can be large` | `T3/GroupTheory/Free/CommutatorRank.lean` と `T3/LinearAlgebra/ExteriorContraction.lean` の `sigmaTwo_pairedCommutator`、`pairedCommutator_rank_le`、`pairedCommutator_cardinalRank_le` | `αₙ = Σ x₂ᵢ ∧ x₂ᵢ₊₁` の収縮から `2n` 個の独立な方向を回復する原稿の経路。一般の `D` に対する結論は cardinal rank で述べ、非有限生成群を落とさない。 |
| Lemma 5.4、1426–1446、`lemma:amalgam over the cyclic group` | `T3/GroupTheory/Amalgamation/Cyclic.lean` の `exists_cyclic_retraction`、`cyclic_amalgamableOver_iff`、`cyclicToFreeThree_amalgamableOver_iff` | derived にある場合は非零 triple の矛盾。derived の外では第 1 層の線形汎関数から retraction を作り、直積で amalgam を作る。base の指定生成元を第一自由生成元へ写す同定を保持する。 |
| Proposition 5.5、1453–1472 | `T3/GroupTheory/Free/UnboundedWitnessRank.lean` の `pairedCyclic_strict_cardinalRank_le`、`pairedCyclic_obstruction_cardinalRank_le`、`exists_cyclic_without_bounded_strict_envelope`、`exists_cyclic_without_bounded_obstruction` | 同じ有限巡回 base と固定された rank 3 の因子について、任意の候補 `D` に `2n` の下界。`d(Aₙ)=1`、`d(F₃)=3`、base の非自明性・有限性も実際の宣言で保持する。 |

## 定数・符号・境界の場合

- η₃ の混合成分の順序は `(2,1)`、`(1,2)` の順。
  `Commutator.lean` の `relator_bracket_blocks` は
  `(-[u,s], -(u ⊗ t), -(s ⊗ q), [q,t])` を返し、
  Lemma 4.7 の符号と一致する。関係**部分空間**の和について符号を消せることと、
  canonical な bracket **写像**の符号を区別している。
- η₁ の全単射性は原稿の自由表示を短縮し、coproduct の普遍性と retraction から
  同じ canonical map について直接証明する。η₂、η₃ は原稿の自由表示と商の経路。
  これは以前の対応表にも明記されている実装上の差で、今回の移行で生じた差ではない。
- Lemma 4.10 の `3 * n.choose 2` は整数除法で弱い上界に変更したものではなく、
  原稿の正確な `3n(n−1)/2` に対応する。defect の rank 評価で第 1 の strictness を
  使う箇所を `exists_lowerCentral_defect_generators` で確認した。
- Proposition 4.13 の算術は
  `3n + 3 * (3n).choose 2 + 2 ≤ 15n²`。
  `n > 0` を用いるのは非自明な `C` の分岐だけである。`C = 1`、特に `n = 0` は
  `D = C` で処理し、`F₂` の二生成元をゼロ上界に押し込めない。
- commutator roots と triple roots は空の有限 family を許す。
  ambient 群の有限性や非自明性を要求しない。
- e.c. の transfer には `IsExistentiallyClosedAt` を使い、元のモデルと拡大を
  独立の universe に置ける。strict envelope の代数的拡大は同じ universe に
  構成できるので追加の cardinality 制限を課していない。
- §5 の `d(D)` は有限生成群にだけ意味を持つ自然数値 `Group.rank` にすり替えない。
  非有限生成 `D` には `Group.cardinalRank` を使い、有限生成の場合との一致は
  `T3/GroupTheory/GeneratorRank/Cardinal.lean` の `cardinalRank_eq_rank` で与える。

## 原稿への提案（未適用）

`notes/v8-paper-review-2026-09-24.md` の指摘を、受領 v9 と現在の Lean に
再照合し、§4–5 について以下の表現上の提案を記録する。
ユーザーの「TeX 自体は変更しない」という指示に従い、以下は採用する原稿に
適用していない。数学的な照合結果は受領版についての判定として維持する。

1. 受領版 844 行、§4 冒頭。
   `G` を導入する前の “a relatively free presentation of G” を
   “a relatively free presentation of a group of exponent 3” とすると、
   次の段落で `G` を導入する順序と整合する。
2. 受領版 1371 行、Example 5.1(2)。
   未導入の `H ≥ G` を “for any H in V₃ containing G and any b,c in H” とすると、
   四重交換子が消えるために用いている、指数 3 の ambient という文脈が明示される。
   Lean の `nonStrict_not_amalgamable` は既にその `HasExponentThree` 条件を
   amalgam の定義から取り出して使用している。
3. 受領版 1451 行、Proposition 5.5 の前。
   自由因子の生成元名を `F₃(s,y,z)` から `F₃(s,x,y)` に揃えると、
   直前の Lemma 5.4 と同じ記号になる。同定 `aₙ ↦ s` はいずれの場合も同じ。

上記の提案も含め、採用する TeX 本文には修正を加えない。
PDF のレイアウト確認はこの静的照合とは別の検査である。
