# 同時交換子 roots・e.c. 群・support の検証境界

> Historical T3 revision identifiers have been omitted for publication. Recorded commands, outcomes, and source hashes describe the original checks; this edited record does not certify the rewritten historical snapshots.

2026-09-10。対象原稿の SHA256 は
`79745dfa1660a827c51ec3c6b2006ee9d6243cb4702f97a75e5b55357b89f50b`。
全論文の形式化 goal は継続中である。今回の80モジュールの全検査は警告0で通過した。

## 固定した検証結果

`python3 scripts/check.py` の build、import 集約、environment lint、text lint、公理監査、
論文対応検査の6段階がすべて終了コード0・警告0となった。入力は検査中に変化せず、
成果物保存前にも live ファイルの SHA256 と照合した。pin 済み Lean/mathlib のローカル
キャッシュを使った検証であり、mathlib 自体のクリーンビルドや CI 実行を意味しない。

対象は集約を含む80モジュール・2,481宣言。許可・実依存公理は `propext`、
`Classical.choice`、`Quot.sound` のみである。対応表は50項目・75部分項目で、
39 proved、5 partial、6 planned となった。

数学ソース revision は
`b6d901b5f03089873409af74e0de6236f8f35350ba89106b8a763e67926b4b64`。
これは `T3.lean` と `T3/**/*.lean` の path-to-SHA256 辞書を `sort_keys=True` で JSON 化し、
再び SHA256 を取った値である。設定・検査・対応表を含む全入力ハッシュ、全宣言一覧、
6段階のログは [保存成果物](audit-artifacts/2026-09-10/commutator-roots-support/README.md) にある。

## Lemma 4.6 の同時商と単射性

`GroupTheory/Roots/Commutator` は、任意の指数3群 G と derived subgroup の有限族 gᵢに対し、
原稿どおり `H₀ = G ∐ Free(Fin(2*n))`、`rᵢ = gᵢ⁻¹[xᵢ,yᵢ]`、
`H = H₀ / normalClosure(range r)` を構成する。`baseMap_injective` は G から H の自然写像の
単射性、`baseMap_root` は指定された新生成元による交換子の等式を与える。
任意 rank、n=0、gᵢ=1 を含み、根を一つずつ追加する構成には置き換えていない。

Claim A では前回の同時 normal word と、normal closure が K[K,H₀] に等しい一般補題を使う。
実際の積としての membership と、singleton normal closure の F₃ 係数による表示も公開した。
同時積の整数係数は、指数3条件により F₃ へ還元する。

Claim B は、自由因子の実際の第二層で異なる `(2*i,2*i+1)` の基底成分を読み、
base の像に入る normal word の全係数が F₃ で0になることを示す。
すると群の語自体が `∏[rᵢ,hᵢ]` に等しくなる。

Claim C は η₃の逆写像による四成分を実際に展開する。
`gr₁(hᵢ)=sᵢ+tᵢ`、`qᵢ=xᵢ∧yᵢ` のとき、成分は
`(-[gᵢ₂,sᵢ], -gᵢ₂⊗tᵢ, -sᵢ⊗qᵢ, [qᵢ,tᵢ])` である。
base の像に入るなら `(1,2)` 成分の和は0で、tensor の右基底成分を読むと全 sᵢが0になる。
純左成分も0となり、第三層の元が0であることと γ₄=1 から元そのものが1となる。
原稿の成分分離・符号・量化を独立担当が照合した。

## Proposition 4.11 の三つの結論

`ModelTheory/ExistentiallyClosedGroups` は、e.c. T₃モデル M に対し、
上下中心列の逆順での一致、derived subgroup の単一交換子表示、第三下中心項の単一三重交換子
表示を証明する。M とその拡大は、既存 e.c. 定義の canonical semantic universe に属する。
新たな有限性・非自明性の仮定は加えていない。

有限個の witness とパラメータを含む有限生成部分群を取り、T₃の局所有限性で有限にする。
有限図式による embedding を M に戻し、パラメータ全体の固定を証明する。
その embedding で交換子の等式と不等式を運ぶ。
単一交換子・三重交換子はそれぞれ同時 root 商を n=1 に特殊化して得る。
中心列一致は、非自明性を e.c. から導いた後、M∐F₂の strictness と二つの graded separation
claim で witness を作り、M に戻す原稿の経路で証明する。
この転送と三つの結論も独立担当が照合した。

## Lemma 3.2 の正確な support bound

`GroupTheory/Support/Collection` と `Support/Conjugator` は、class 2 の群で B の生成列に
沿って交換子を収集する。生成列の各元に対する交換子の表示を closure induction で B 全体へ
拡張する。このため、収集した積は B の生成元数 m に応じた m 個の混合交換子で足りる。
H/γ₃(H) で収集し、G 成分を持ち上げると、高々 m+1 個の G の元で同じ共役作用を実現できる。
原稿の右共役 `u⁻¹δu=v⁻¹δv` を公開する。積順序と混合交換子の向きの変更は、同じ中心的な
収集式の係数に吸収でき、必要な G の生成元を増やさない。

`GroupTheory/Support` は各 principal normal closure の幅3を使い、高々 `3(m+1)` 個の
G の元を集める。有限 relator 族の normal closure を principal normal closure の積に分解し、
得た支持の有限和集合 Y を取ると `Y.card ≤ 3(m+1)n` になる。
`C=⟨Y⟩≤G` とし、`H₀=⟨C,B,Δ⟩` 内で証明書を得る。

`normalClosureIn H₀ Δ` は H₀ 内の `normalClosure(H₀.subtype ⁻¹' Δ)` を ambient に写した
実際の部分群であり、単に ambient H の normal closure を再利用する定義ではない。
`exists_bounded_support_set` は任意の集合 Δ の `encard≤n` を受け取り、この仮定から有限性を
導いて Finset 版を適用する。無限集合の `ncard=0` を使う穴はない。
`exists_bounded_support_rank` は mathlib の `Group.rank` による `d(C)≤3(m+1)n` と内部の
normal-closure certificate を同時に与える。
空の relator 族、m=0、n=0、無限の ambient 群を含む。
有限族の集約、内部 normal closure、定数、空の場合も独立担当が照合した。

## 残る主要な作業

Lemma 4.7・4.9 の defect 商空間の基底選択と二段階 strictification、Proposition 4.12 の
内部中心列一致 envelope と `15n²`、amalgamation の群論的表示と主定理の witness bound、
無条件の model companion 存在が未完成である。残る記法・例・Remark 4.10 と、一般の
semantic universe bridge も全体 goal に残す。

前回の75モジュールの検証記録・成果物は
[graded coproduct と一般 amalgamation 判定](graded-coproduct-and-amalgamation-checkpoint.md)
に固定したまま保持する。原稿は `[historical revision omitted]`、そこまでの Lean ライブラリは
`[historical revision omitted]` にコミット済みである。
