# Graded coproduct と一般 amalgamation 判定の検証境界

2026-09-10。対象原稿は `T3_modelcompanion_v4.tex`、SHA256
`79745dfa1660a827c51ec3c6b2006ee9d6243cb4702f97a75e5b55357b89f50b`。
全論文の形式化 goal は継続中である。

全ライブラリ検査の6段階が警告0で成功した。入力のハッシュを再照合し、
[検査成果物](audit-artifacts/2026-09-10/graded-coproduct-amalgamation/README.md) を保存した。
主要な追加証明は実装担当とは別の担当も読解して原稿と照合した。

## Proposition 4.3 の完成

`Coproduct/GradedEquiv.lean` の `layerTwoEquiv` と `layerThreeEquiv` は、前回実装した
canonical な η₂・η₃そのものを underlying map とする線形同型である。
有限群・有限 rank の仮定はない。原稿の自由表示からの商の経路を保った。

まず `ExteriorLowDegree` が、外積の一般 tensor 分解を次数2・3の表示に並べ替える。
`FreeGraded` ではこれと自由群の σ を用い、自由因子の場合の canonical な η の
全単射性を証明する。η₃ の右混合 `(1,2)` 成分は通常の外積との間に負符号を持つ。
この符号を同型に組み込み、実際の写像との一致を証明している。

次に `QuotientMaps` が、左右の全射自由表示による block 写像の kernel を計算する。
tensor 写像の kernel は左右の kernel の tensor 像の和であり、前回の normal closure の
関係像と一致する。`GradedQuotient.mapLayer_ker` で一般の全射準同型の graded kernel を
その群 kernel の ambient graded image と同定する。自然性の可換四角形と kernel の一致から、
canonical な η₂・η₃が商に降りても全単射であることを得る。
一般群に必要な自由表示は、その第一層の基底と代表元から Proposition 4.1 により供給する。

`BlockBracket` は、実際の graded Lie algebra 内に純成分と混合 tensor 像の block を定義し、
すべての次数で `[block(i,j), block(k,l)] ⊆ block(i+k,j+l)` を証明する。
高次数・次数0も実際の部分空間の消滅から扱う。混合 bracket の符号付き公式も公開した。

これにより Proposition 4.3 の両項目が完成した。η₁だけは前回記録どおり、原稿の自由表示
経由を短縮して coproduct の普遍性と retraction から同じ写像を証明している。
原稿の単なる abstract 同型と別の写像を同一視したものではない。

## Lemmas 4.4・4.5

`Coproduct/Strict.map_injective_of_strict` は、strict な包含 `D ≤ G` が誘導する
`D ∐ B → G ∐ B` の単射性を証明する。η₁–η₃の自然性と、体上で tensor 積が単射性を
保つことから graded 各層の単射性を得て、Proposition 2.24 を適用する。
G・Bの有限性や有限生成性は不要である。

`Coproduct/CentralSeries.freeTwo_stabilization` は、非自明な任意の指数3群 G に対し、
G の自然な像が `G ∐ F₂` 内で strict であり、後者の上下中心列が逆順に一致することを証明する。
`FreeTwoSeparation` は原稿の二つの claim の成分分岐をそのまま扱う。
第一層は左右の成分、第二層は α₂・α₁・α₁′・β₂の順に分ける。
η₃の逆写像で所要成分を取り出して非零を示すため、異なる成分間の相殺は起こらない。
`CentralSeriesCriterion` で実際の群の交換子と中心列へ戻す。
原稿の任意の非自明群と F₂ の証明を完成した。

## Fact 2.6 の両方向

`ModelTheory/BoundedAmalgamationCriterion.hasModelCompanion_iff_boundedAmalgamationObstructions`
は、有限言語の一般 Π₂・局所有限理論 T について Fact 2.6 全体を証明する。
有限構造 A・B・障害 C 自体に T-model 条件を要求せず、空の構造が許される言語も扱う。
amalgamation は共通部分上で一致する二つの embedding の存在であり、strong amalgamation
の条件は加えない。上界は A・B の有限包含を固定してから選び、全 e.c. モデルとその中への
A の embedding に共通である。C の生成元は A の生成元も含む総数で数える。

必要方向では、有限拡張の実現を表す存在式の否定を model companion 上で存在式に置き換え、
構文からモデルに依存しない witness 数を得る。その witness と A の像が生成する C を取る。
C と B の amalgam があれば、それを model companion のモデルに埋め込み、互いに反する
二つの存在式が同時に実現するため矛盾する。

十分方向では、一様局所有限性から有界生成障害の共通位数上界を取る。
有限台集合上の全関数・関係表と A の marking を有限個並べ、実際の障害から来るものだけを
選ぶ。`FiniteObstructions.exists_finite_bad_marked_cover` は任意の障害に対して、A を固定する
構造同型により代表を与える。重複した同型型は有限連言に影響しない。
`ExtensionAxioms` の実際の文は、A の図式とすべての悪い拡張の不在から B の拡張を要求する。
これらの文の理論がちょうど e.c. モデルを公理化することを、有限生成部分構造への witness
の閉じ込めと有限図式で証明し、Fact 2.3 に接続する。

一般の companion・e.c. のモデル量化は従来の canonical semantic universe 規約を継承する。
この規約を任意の上位宇宙のモデル量化へ移す一般 bridge は、別の残件である。
有限構造の符号化により対象の量化を勝手に縮めたものではない。

## 実際の T₃ への接続

`ModelTheory/GroupLanguage` は群言語・群公理、モデルの元の演算からの群構造の復元、
embedding と単射群準同型、substructure と subgroup の対応を与える。
`ExponentThree` は `Tₙ = group theory ∪ {∀x, xⁿ=1}` を定義し、T₃と `HasExponentThree` の
同値、有限言語・Π₂・局所有限性を供給する。有限生成群は有限自由指数3群の像なので有限である。
代数的主張と有限生成部分構造の有限性は任意宇宙で証明し、自明群・空の生成集合も含む。

`exponentThreeTheory_hasModelCompanion_of_boundedAmalgamationObstructions` は、群論的な
有界障害を仮定する最後のモデル理論的な橋である。仮定を供給する Theorem 3.3 はまだ未完成で、
この橋だけを Corollary 3.4 の証明とは数えない。

## 同時交換子 roots の現在の境界

`Roots/CommutatorRelations.exists_normalWord` は、derived subgroup 内の有限 relator 族の
normal closure に属する任意の元を、一つの積 `∏ᵢ rᵢ^mᵢ [rᵢ,hᵢ]` に表す。
係数は整数で、原稿の F₃ 係数への還元は後続の作業である。任意群・n=0を含む。
個々の共役に対する式と、derived subgroup の可換性による積・逆元での閉性を用いる。
これは Lemma 4.6 の Claim A で使う同時積表示だけである。
具体的な `G ∐ F₂ₙ` の一括商、Claim B/C、base embedding の単射性はまだ未完成である。
singleton normal closure の集合等式も、この新モジュール単独では主張していない。

## 生成元数と次数1・2の次元

`GroupTheory/GeneratorRank` は有限生成群の最小生成元数に mathlib の `Group.rank` を使い、
別の定義を作らない。有限生成族から自由群の全射を得て、実際の graded 各層にも全射を誘導する。
自由群の有限支持座標の基底から、`dim gr₁(C) ≤ m` と `dim gr₂(C) ≤ binom(m,2)` を証明した。
有限次元性も全射により別に供給しており、無限次元の場合の `finrank` の既定値は使わない。
生成族の添字には有限性だけを要求し、群全体の有限性・基底順序は仮定しない。
空の生成族も含む。これらは Lemmas 4.7・4.9 の次元評価の段階であり、defect 商空間の
基底選択・具体的な strictification の構成はまだ証明していない。

## 全体の残件と検査

次は同時交換子 roots の単射性、defect 商空間の基底選択、二段階 strictification、
e.c. 転送を組み立てる。`15n²` の内部中心列一致 envelope、`3(m+1)n` の support、
主定理の `f(m)=15*((3*m+4)*t(m)+1)^2`、model companion の存在と残る例・記法が未完成である。
定数は各結果に対応するモジュールに置く。

`python3 scripts/check.py` の build、import 登録、environment lint、text lint、公理監査、
論文対応表の6段階がすべて exit code 0・警告0で成功した。
固定済み Lean/mathlib の cache を用いたローカル検証であり、mathlib の clean build や CI ではない。

- 数学モジュールは集約を含めて75。
- 公理監査は private を含む2,316宣言。private 名385、public 名1,931で、public 名はすべて export 済み。
- export 済み監査対象は1,946名。生成された private 名の equation lemma・splitter 15件も含み、
  private と exported のフラグは排他的ではない。
- 実際の公理依存は `propext`、`Classical.choice`、`Quot.sound` のみ。`sorryAx`・独自公理はない。
- 論文対応表は全50項目中 `proved` 36、`partial` 6、`planned` 8。
  項目数は数学的難度で重み付けした完成率ではない。主定理と系は未完成である。
- 数学ソース revision は
  `698dc3a221b576e31035d9440bcc24d9fba16ad95a9e882b6ef718084d660653`。
  `T3.lean` と `T3/**/*.lean` の path-to-SHA256 辞書を `json.dumps(..., sort_keys=True)` した SHA256。
- 全検査入力のハッシュと6段階の結果は `checks.json`、宣言の公理依存と可視性は
  `declarations.json` に保存した。

対応表の検査では、指数条件の登録に `GroupTheory.Basic` を引き続き必須としつつ、
今回追加した実際の一階理論のモジュールも併記できるようにした。
source locator・宣言の実在・export・公理検査は保持している。

前回の53モジュールの記録と成果物は
[Coproduct の tensor 分解と model companion 判定](coproduct-tensor-and-companion-checkpoint.md)
に変更せず保持する。
