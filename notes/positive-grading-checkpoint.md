# 正次数 graded Lie の定義と生成条件の検証境界

> Historical T3 revision identifiers have been omitted for publication. Recorded commands, outcomes, and source hashes describe the original checks; this edited record does not certify the rewritten historical snapshots.

2026-09-10。Definition 2.7 と Remark 2.8 を対象とする。
94モジュールの全体検査が終了コード0・警告0で通過した。

## 固定した検証結果

`python3 scripts/check.py` の build、import 集約、environment lint、text lint、公理監査、
論文対応検査の全6段階が通過した。検査中の入力不変性と成果物保存時の live SHA256 一致を
確認した。pin 済み Lean/mathlib キャッシュによるローカル検証であり、mathlib 自体の
クリーンビルドや CI 実行ではない。

94モジュール・2,642宣言を監査した。private-name 宣言498、public-name 宣言2,144で後者は
すべて exported。exported な監査対象名は2,160であり、private-name の生成補題16個と重複する。
許可および実際の公理集合は `propext`、`Classical.choice`、`Quot.sound` のみ。
対応表は50項目・75部分項目、47 proved・2 partial・1 planned。この集計は作業量の完成率ではない。

原稿 SHA256 は `79745dfa1660a827c51ec3c6b2006ee9d6243cb4702f97a75e5b55357b89f50b`、
数学ソース revision は `2ef0132ae129a20ad6d8cc61a2dab5b9648d3882b57201f8d85bfa65feb4b915`。
後者は `T3.lean` と `T3/**/*.lean` の path-to-SHA256 辞書を `sort_keys=True` で JSON 化した
ものの SHA256 である。全入力・全宣言・6段階のログは
[保存成果物](audit-artifacts/2026-09-10/positive-grading/README.md) に固定した。

## 実装した定義

`T3/LinearAlgebra/GradedLie.lean` は mathlib の `LieRing`、`LieAlgebra`、
`GradedLieAlgebra` を使用する。原稿の正次数直和は、自然数次数の実際の直和分解と
次数0の成分が零である条件 `IsPositive` によって表す。
係数環を任意の可換環 R として証明し、R=ℤ は Lie ring、R が体の場合は Lie algebra を与える。
有限次元性・有限 rank・標数の条件は不要である。

## Definition 2.7

native class の bracket の双加法性・交代性・左入れ子の cyclic Jacobi を公開する。
逆に原稿の双加法的・交代的 bracket と cyclic Jacobi から native `LieRing` を作る
`LieRing.ofCyclicJacobi` を与える。mathlib の Leibniz 形式と原稿の左入れ子の形式の
差異を証明で埋めており、単に異なる公理系を同じ名前で呼んでいない。
`GradedLieAlgebra` の bracket 整合性から各次数の包含を与える。

## Remark 2.8

反対称性を交代性から得る。`[Lᵢ,L₁]` は単一の bracket の集合ではなく、
それらが生成する submodule として `Submodule.map₂` で表す。
原稿の Lie ring の場合は、この submodule の係数環を ℤ とする。

順方向では、L₁ と繰り返し右から bracket を取ってできる submodule を Rₙ とし、
Jacobi identity を使って、その上限が L₁ の生成する Lie algebra を含むことを示す。
L₁ が L を生成するとき上限は全体となる。Rₙ は対応次数の成分に含まれ、実際の
graded 分解の射影を使うと、その成分は逆に Rₙ に含まれる。したがって全 i≥1 に
`[Lᵢ,L₁]=Lᵢ₊₁` が成立する。

逆方向では、この bracket 等式から次数について帰納し、全ての正次数成分が
L₁ の Lie span に入ると証明する。次数0は `IsPositive` から零である。
実際の直和分解の帰納法により全体が生成される。
このため正次数の仮定は逆方向に必要で、順方向には追加していない。

原稿・native class の公理・次数0・bracket の線形 span 解釈・全次数での両方向を
独立担当と root が照合した。

## 対応表の宣言名検査

対応表の字句検査が ASCII 名だけを受け付け、`map₂` を `map` までしか読んでいなかったため、
通常の Unicode 識別子を受け付けるようにした。三つの実際の添字付き宣言の全名と元の行番号を
確認し、切り詰めた名前が現れないことを検査した。最終の公理監査の manifest とも照合する。
これは字句上の所在検査の修正であり、数学的な対応の判定を自動化したものではない。

## 残件

主定理と model companion の存在は前回の
[93モジュール境界](main-theorem-checkpoint.md)、コミット `[historical revision omitted]` に固定したまま保持する。
今回の変更後も、Remark 4.10、残る記法と Example 2.21、一般モデル宇宙への bridge が残る。
全論文の goal は継続中である。
