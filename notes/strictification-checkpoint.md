# 基底による二段階 strictification の検証境界

> Historical T3 revision identifiers have been omitted for publication. Recorded commands, outcomes, and source hashes describe the original checks; this edited record does not certify the rewritten historical snapshots.

2026-09-10。原稿 SHA256 は
`79745dfa1660a827c51ec3c6b2006ee9d6243cb4702f97a75e5b55357b89f50b`。
この記録は Lemma 4.7・4.9 の構成とその前提を扱う。全論文の goal は継続中である。
84モジュールの全検査が終了コード0・警告0で通過した。

## 固定した検証結果

`python3 scripts/check.py` の build、import 集約、environment lint、text lint、公理監査、
論文対応検査の6段階がすべて通過した。検査中の入力不変性を確認し、成果物保存時にも
live ファイルの SHA256 と比較した。pin 済み Lean/mathlib キャッシュによるローカル検証であり、
mathlib 自体のクリーンビルドや CI 実行ではない。

集約を含む84モジュール・2,545宣言を監査した。private-name 宣言は480、public-name 宣言は
2,065で、後者はすべて exported。exported な監査対象名は2,081であり、生成された private-name
の equation/splitter 16個は exported にも数える。二つのフラグは排他的ではない。
実依存公理は許可した `propext`、`Classical.choice`、`Quot.sound` のみである。

対応表は50項目・75部分項目、状態は41 proved・3 partial・6 planned。
これは項目別の集計であり、作業量に対する完成率ではない。
数学ソース revision は
`d86762cb017ab8a27f8e33c6f717027eb2f8930df5d71b17508576b04d3706f8`。
`T3.lean` と `T3/**/*.lean` の path-to-SHA256 辞書を `sort_keys=True` で JSON 化したものの
SHA256 である。全入力・全宣言・6段階のログは
[保存成果物](audit-artifacts/2026-09-10/strictification/README.md) にある。

## 実際の欠損商の基底

`Roots/DefectBasis` は `mapLayer f k` の kernel W の有限基底を選び、各基底ベクトルを
`term G k` の元 gᵢに持ち上げる。その gᵢの像は ambient の次の下中心項に入り、
次の正確な部分群等式を証明する。

`comap f (term H (k+1)) ∩ term G k = term G (k+1) ⊔ closure(range g)`。

基底の個数は `finrank W ≤ finrank (Layer G k)` を満たす。有限次元性を仮定または証明して
から finrank を使い、無限次元での自然数 finrank の既定値には依存しない。
包含写像の第一層では W が `(C∩γ₂(G))/γ₂(C)` に対応する。
第二層では初めから分子は `γ₂(C)∩γ₃(G)` であり、第一の strictness 等式を使って初めて
`C∩γ₃(G)` と一致する。この仮定を外していない。

第一層・第二層の生成元数による次元上界を接続し、それぞれ高々 `Group.rank C` 個、
高々 `(Group.rank C).choose 2` 個の代表元で十分と証明する。基底0個の場合も含む。
この基底の構成と分子の同定は独立担当が原稿と照合した。

## Lemma 4.7 の同時交換子商

`Roots/DerivedStrictification` は、この欠損族に対して Lemma 4.6 の同時商
`(G ∐ Free(Fin(2*d))) / L` を用いる。D は C の像と新自由生成元から生成する。
一次商で自由因子と C の成分を分離し、自由側は derived subgroup へ入り、C 側の欠損は
指定 root equations と上の生成等式で D 自身の derived subgroup へ入る。
原稿の同時商と一次成分の議論を保ち、単根を順に付ける反復には置き換えない。
商の一次部分と生成等式、`2m` 個の付加・`3m` の総 rank の接続を別担当が全文照合した。

## Lemma 4.9 の同時三重交換子商

`Roots/LowerCentralStrictification` は第二の欠損族に対して Lemma 4.8 の商
`H=(G × Free(Fin(3*d)))/L` を用いる。D を `C × Free(Fin(3*d))` の商への像として定義し、
C の像と `3*d` 個の新生成元で生成することを証明する。

関係部分群が ambient の γ₃ と `C × F` の内部の γ₂ に含まれることを公開する。
また L が `C × F` に含まれるので、商への写像で部分群の交叉を正確に計算できる。
γ₂ ではもとの strictness 等式と直積の中心列の式を使う。
γ₃ では欠損を内部の γ₃ と gᵢで生成し、gᵢの像が D 内の三重交換子となるため欠損が消える。
この D の二つの交叉等式から `IsStrict D` を得る。

終端は `Group.rank C ≤ m` のもとで `3 * m.choose 2` 個以下の付加生成元を与える。
さらに D の有限生成性と総生成元数 `Group.rank D ≤ m + 3 * m.choose 2` も返す。
拡大 H は G と同じ宇宙にあり、ambient の有限性・非自明性を仮定しない。
kernel 包含、商内の交叉、追加数と総数、m=0/1 と空の基底も独立担当が照合した。

## 補助補題と残件

join の積分解と片側 kernel 包含下の交叉像の等式は
`GroupTheory/Subgroup` の標準 namespace で証明した。指数や有限性の仮定は不要である。
直積の中心列は pin 済み mathlib の既存定理を利用する。
直積・商・交叉を計算し、欠損の基底から選んだ族について同時 strictification を構成する。

前回の80モジュール・2,481宣言の成果物は
[同時交換子 roots・e.c. 群・support](commutator-roots-and-support-checkpoint.md) と
コミット `[historical revision omitted]` に固定したまま保持する。
次はこの二段階から内部中心列一致の有限部分群を作り、e.c. 転送で Proposition 4.12 の
`15n²` を証明する。主定理の群論的 amalgamation 表示・witness bound、無条件の model
companion の存在、残る例・記法・Definition 2.7 と Remark 2.8・共有 triple roots と一般宇宙の
bridge は未完成である。

次の接続に必要な API は、有限生成指数3群の有限性、coproduct の有限生成性と
`rank(G∐F₂)≤rank G+2`、同型による `CentralSeriesCoincide` の輸送である。
一方、有限の D₃ を M に戻す部分は既存の `ExistentiallyClosedGroups.exists_group_embedding`
を使える。共通の有限パラメータ型を C、返る embedding の range を D とすれば C 全体を固定する。
range の有限生成性と rank 評価には mathlib の `Group.fg_range` と `Group.rank_range_le` を使う。
最終的な strictness は `isStrict_of_centralSeriesCoincide` による。

原稿の C=1 の分岐は残す必要がある。この場合 D=1 とすれば内部中心列一致と bound が成り立つ。
非自明な C の場合だけ rank の正性から n≥1 とし、D₂ の非自明性を包含の単射性から得て F₂ を
付ける。C=1 でも一律に F₂ を付ける方法では n=0 の `15n²` を満たさない。
