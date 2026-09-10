# 主定理と model companion の存在の検証境界

> Historical T3 revision identifiers have been omitted for publication. Recorded commands, outcomes, and source hashes describe the original checks; this edited record does not certify the rewritten historical snapshots.

2026-09-10。Theorem 3.3 と Corollary 3.4 を対象とする。
93モジュールの全体検査が終了コード0・警告0で通過した。
一般モデル宇宙への bridge と残る論文項目のため、全論文の goal は継続中である。

## 固定した検証結果

`python3 scripts/check.py` の6段階――build、import 集約、environment lint、text lint、
公理監査、論文対応検査――がすべて通過した。実行中の入力不変性と成果物保存時の
live SHA256 一致を確認した。pin 済み Lean/mathlib キャッシュによるローカル検証であり、
mathlib 自体のクリーンビルドや CI 実行ではない。

集約を含む93モジュール・2,620宣言を監査した。private-name 宣言488、public-name 宣言2,132で
後者はすべて exported。exported な監査対象名は2,148であり、private-name の生成補題16個と
重複する。許可および実際の公理集合は `propext`、`Classical.choice`、`Quot.sound` のみ。
対応表は50項目・75部分項目、45 proved・2 partial・3 planned。この集計は作業量の完成率ではない。

原稿 SHA256 は `79745dfa1660a827c51ec3c6b2006ee9d6243cb4702f97a75e5b55357b89f50b`、
数学ソース revision は `59bf3bacaa6981adddf1d216ff2a71f2b9d8bc23e3512909e25883280251f699`。
後者は `T3.lean` と `T3/**/*.lean` の path-to-SHA256 辞書を `sort_keys=True` で JSON 化した
ものの SHA256 である。全入力・全宣言・6段階のログは
[保存成果物](audit-artifacts/2026-09-10/main-theorem/README.md) に固定した。

## 原稿の位数と生成元数の評価

`GroupTheory/GeneratorRank/Cardinality` は、有限生成指数3群で
`Group.rank G = finrank (ZMod 3) (Layer G 1)` を証明する。
第一層の有限基底の代表元を選び、Proposition 4.1 の自由表示が全射であることを使う。
無限次元の場合の `finrank = 0` には依存しない。
第一層の位数は `3^rank G` であり、G からこの商への全射がある。
逆に、最小生成集合上の自由群から G への全射と正規形の位数公式から
`|G| ≤ 3^t(rank G)` を得る。

これにより、単射 `A → B` と `rank B ≤ m` から原稿の列
`rank A ≤ Nat.log 3 |A| ≤ Nat.log 3 |B| ≤ t(rank B) ≤ t(m)` を証明する。
`Nat.log` は実対数の床に相当する整数評価に用いている。
B の有限生成性と指数3性から A の有限性・有限生成性・指数3性も導出できるため、
終端には A の有限生成性を追加仮定にしない package もある。

## Theorem 3.3 の証明

`Main/BoundedWitness` で `witnessBound m = strictEnvelopeBound ((3*m+4)*freeOrderExponent m+1)`
を定義する。すなわち原稿どおり `15*((3*m+4)*t(m)+1)^2` である。
上界の引数は B の生成元数だけである。

A の最小生成集合 s に対する relators Δ について、amalgam の商表示から左右どちらかの
非自明元を得る。`Coproduct/Support` は Lemma 3.2 が返す support を左因子へ引き戻し、
高々 `3(m+1)|s|` 個の元 Y を選ぶ。ここでの証明は、原稿の H₀ の内部で計算した
normal closure に属するという情報を保つ。

M 内では `S = Y ∪ sの像 ∪ Z` とする。左の証人 x の場合は `Z={x}`、右の場合は `Z=∅`。
`|S| ≤ 3(m+1)|s|+|s|+1 ≤ (3m+4)t(m)+1` を証明し、その閉包 C に Proposition 4.12 を適用する。
A 全体は s から生成されるので A≤C≤D となり、D の総生成数は `witnessBound m` 以下である。

D の strictness により `Φ : D ∐ B → M ∐ B` は単射である。
H₀ は Φ の range に入り、`Support/Transport` の包含先への単調性と逆写像を使って
内部 normal closure の証明を引き戻す。この逆写像は関係元だけでなく共役元も引き戻す。
Φ が D 側の各 relator を M 側の同じ relator に写し、かつ単射なので、
`Φ⁻¹(Δ_M) = Δ_D` という集合等式が成立する。生成族の relators と全 base の relators の
normal closure の等式を使い、D または B の非自明元が canonical quotient で消えると示す。
従って D と B は元の A 上で amalgamate しない。

終端 `exists_bounded_nonamalgamation_witness` と、モデル・base に一様な関数を存在量化した
`exists_uniform_nonamalgamation_bound` の両方を公開する。
M は canonical semantic `Type`、B は任意宇宙、零 rank と自明群も含む。
原稿の左右両分岐・全生成数・内部証明の移送を独立担当が照合した。

## Corollary 3.4 への接続

`ModelTheory/GroupAmalgamation` は実際の群の amalgam と T₃ の一階構造の amalgam を
双方向に接続する。因子の model 性は前提にせず、target のみが T₃ のモデルである。
双方の target 構造を実際に作り、元ごとに同じ可換図式を保つ。

`Main/ModelCompanion` は一般の有限 inclusion d に対し、d.ext の embeddability と
T₃ の普遍性からその T₃-model 性を回復する。base の群構造も d.incl を通じて回復する。
M と base の embedding を量化する前に、bound を `witnessBound(rank d.ext)` に固定する。

base の M への像 A と元の base の群同型 q を使い、Theorem 3.3 の実際の部分群 A に移る。
q を前合成すれば元の二つの embedding に戻り、返る obstruction も q の逆で元の base に戻る。
生成元数は D 全体の最小生成集合を M に写して `GeneratedByAtMost` を供給するため、
base を除いた相対的な生成元数ではない。

群の部分群 D と一階の部分構造 C は同じ元を持つが、Group instance の定義的一致を
仮定していない。C のモデル性から群構造を回復し、同じ元を保つ実際の単射準同型
`eD : D → C` を構成して obstruction を移す。
この bound を一般の Fact 2.6 に渡し、有限言語・Π₂・局所有限性の既存証明を使う。
終端 `T3.has_model_companion` に追加の未証明仮定は残らない。
base の保持・全生成数・一般 criterion の仮定の供給は独立担当が照合した。

## 完成範囲と残件

ここで主定理と系の canonical semantic universe における証明経路が閉じた。
Definition 2.7、Remark 2.8、Remark 4.10、記法と残る Example 2.21 の部分項目、
一般モデル宇宙への bridge は未完成であり、全論文の goal を完了扱いにはしない。
Remark 4.10 は F₄ の4個の三重交換子の独立性だけでなく、共有する生成元を使う
quotient と strictification、交換子 roots への同様の適用まで確認する必要がある。

前回の87モジュール境界は [strict envelope と商表示](strict-envelope-and-pushout-checkpoint.md)、
コミット `[historical revision omitted]` とその保存成果物に固定したまま保持する。
