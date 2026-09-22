# 無限正規形・中心列と associated graded の次数商

> 履歴資料（v4 原稿）。原稿は [archives/T3_modelcompanion_v4.tex](../archives/T3_modelcompanion_v4.tex) に保存。以下の番号・行・検証結果は当時のもの。
> 現行 v7 の対応は [対応表](../docs/paper-map.md) と [v7 移行記録](v7-migration.md) を参照。

2026-09-09。対象は v4 TeX、SHA256
`79745dfa1660a827c51ec3c6b2006ee9d6243cb4702f97a75e5b55357b89f50b`。
[前回の有限正規形の境界](free-normal-form-checkpoint.md) から進めた記録であり、
論文全体の完成を表さない。

## 任意 rank の正規形

`T3/GroupTheory/Free/FiniteSupport.lean` は、任意の元が有限生成集合上の自由群から
来ること、生成集合の単射が自由群の単射を誘導すること、座標の restriction と
有限支持を証明する。空の生成集合も扱う。有限正規形の3補題には `_of_finite`
を付け、元の名前で任意 rank の比較写像・座標の単射性を公開した。

`T3/GroupTheory/Free/InfiniteNormalForm.lean` は、生成元・increasing pair・
increasing triple 上の `Finsupp` の3係数族から、原稿に表示された積を定義する。
生成元は支持の昇順に掛ける。交換子ブロックは derived subgroup の可換性、
三重交換子ブロックは中心性により、それぞれの内部列挙順によらない。
係数の `ZMod 3.val` を冪指数に用いる。

全射性では、元の次数1座標を取り出し、第一ブロックを左から除いて次数1のkernelへ
移り、次数2の座標を取り出して第二のkernelへ移る。次数3の単射性により残りが
第三ブロックと一致する。一意性は同じ順に readout と cancellation で係数を同定する。
有限版の証明を再利用し、全座標モデル全体と自由群を同一視していない。
`existsUnique_normalWordFinsupp` は任意の線形順序付き `I` についての存在一意性であり、
有限性・可算性・非空性を仮定しない。独立した原稿照合でも Remark 2.28 と一致した。

## 中心列と次数商

`T3/GroupTheory/CentralSeries.lean` では mathlib の既存中心列を用いる。
lower index `n` は原稿の γₙ₊₁、upper index `n` は Zₙ。
一般群のままで Def 2.12、Remark 2.13、Fact 2.14 の内容を証明した。
交換子の次数評価は Three Subgroups Lemma の quotient 版から得る。
任意長の反復交換子による上部中心列の特徴づけ、次数商の可換性も含む。

`IsStrict` は部分群の内部中心列の像と ambient の交わりとの一致、
`CentralSeriesCoincide` は内部での上下中心列の逆順一致を表す。
Def 2.23、Def 2.25、Lemma 2.26 の任意 ambient 内の包含鎖と strictness を実装した。
準同型の像についての条件と comap との同値も証明済みである。

`T3/GroupTheory/AssociatedGraded.lean` は、実際の γₙ/γₙ₊₁ を additive group とし、
標準 `Module (ZMod 3)` を与える。補助的な次数0は零、次数4以上も零である。
任意の群・任意 rank の次数商を扱い、自由群の座標辞書で代用していない。
部分群の graded image は intrinsic な中心列ではなく ambient の交わりから作り、
原稿の quotient との canonical `LinearEquiv` を公開した（Notation 2.20）。
全次数の `DirectSum` と誘導 `LinearMap`、その単射性と群の単射性・strictness の
関係まで証明した。これらの型も別担当者が原稿に照合した。

**Lie bracket と Lie algebra 構造は未実装。** `GradedModule` と呼び、
Def 2.18、Lemma 2.19、Def 2.22、Prop 2.24 の全体は `partial` のままにする。
Prop 2.24 の線形写像についての二つの主張は証明されているが、Lie 構造を備えた
写像への接続が残る。次数1による Lie 生成、外積 Lie algebra との同型も残件である。

## 一般モデル理論

`T3/ModelTheory/Inductive.lean` は、∀∃ 文集合による同値な公理化という
Def 2.2(5) の Π₂ 条件を実装した。universal theory に弱めず、model companion の
各モデルが元の理論のモデルであり e.c. になることを証明した。
これは Fact 2.3 のモデル類の等式の一方の包含であり、Fact 全体の完了ではない。

`T3/ModelTheory/ModelCompleteness.lean` は QF diagram と canonical embedding を構成した。
semantic model completeness の下で真な parameter formula が理論と有限個の
QF diagram 文から従うことを compactness で得た。
semantic から syntactic への逆 bridge は、有限図式の定数を存在量化変数へ戻す操作と、
局所存在公式を有限個にまとめる操作が残っている。companion/e.c. の universe 変更
bridge と一般 bounded-amalgamation criterion も引き続き残件である。

## 検査

`python3 scripts/check.py` は全6 gate が終了値0・警告0で成功した。
18数学モジュール・692宣言を公理監査し、private名の宣言135件を含む。
557宣言の公開性を確認した。依存公理は `propext`、`Classical.choice`、`Quot.sound` のみ。
検査前後および記録保存時の入力ハッシュは一致している。

全体 gate の入力ハッシュ、公開性・公理依存の一覧とログは
[検証記録](audit-artifacts/2026-09-09/infinite-normal-form-graded/README.md) に保存した。
対応表の `code_revision` は全数学ソースの SHA256 辞書を
`json.dumps(inputs, sort_keys=True)` で直列化したものの SHA256 を指す。
今回の値は `e2760b67d2a0dfc9fb89001661f5eab529216bf08b2da05919b9aa9bc180bad0`。
pin済み依存キャッシュを使ったローカル検証で、CI実行やmathlib全体のclean rebuildではない。

次は原稿の代表元による bracket を構成し、Lie 公理・自然性・次数1生成を供給する。
その後に外積 Lie algebra の標準 API へ接続する。一般 coproduct・同時 roots・
`15n²`・support・主定理と系は未完成のままで、長期 goal は継続する。
