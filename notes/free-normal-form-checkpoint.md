# 自由群・有限正規形と coproduct の基礎

> 履歴資料（v4 原稿）。原稿は [archives/T3_modelcompanion_v4.tex](../archives/T3_modelcompanion_v4.tex) に保存。以下の番号・行・検証結果は当時のもの。
> 現行 v8 の対応は [対応表](../docs/paper-map.md) と [v8 移行記録](v8-migration.md) を参照。

2026-09-09。対象は `T3_modelcompanion_v4.tex`、SHA256
`79745dfa1660a827c51ec3c6b2006ee9d6243cb4702f97a75e5b55357b89f50b`。
Lean/mathlib の pin は初期検証と同じ。これは全論文完成とは別の中間境界である。

## 数学的な実装範囲

- `Free/Basic`：通常の自由群を立方の正規閉包で割る `T3.Free`、生成元、普遍性と
  一意性、生成集合の写像が誘導する準同型。Notation 2.1(9) の定義どおり。
- `Free/Model`、`ModelComparison`：Levi–van der Waerden の座標群と比較写像。
  座標群全体と自由指数群を同一視しない。比較写像の像について正規形を証明する。
- `Free/Collection`、`NormalForm`：任意の有限線形順序付き生成集合について、
  有限性、`|F| = 3 ^ (n + n.choose 2 + n.choose 3)`、および Fact 2.27 の表示の一意性。
  `T3.freeOrderExponent` は `NormalForm` に定義した。
- `Free/Examples`：`Free (Fin 2)` で γ₃=1、Z₂=G、Z₂ が非可換であること。
  初期検証の derived subgroup 可換性と合わせ、Fact 2.15(3) の残りを埋める。
- `Coproduct/Basic`：通常の自由積を立方の正規閉包で割る `T3.Coproduct`、普遍性、
  両因子への retraction と単射性、非交和上の自由群との同型。
  Notation 2.1(8)、Fact 2.16、Lemma 2.17。有限性や presentation の仮定はない。
- `ModelTheory/ModelCompanion`：Definition 2.2(1–4)。model completeness は論文の
  「全 formula が existential formula に同値」という構文的定義を採用する。
  この条件から、任意宇宙のモデル間の embedding が全 formula を保存・反映することを証明した。

`Free/` はすべて `T3/GroupTheory/Free/` の略。
公開宣言と原稿中の所在は [対応表](../docs/paper-map.md) に記録する。

## 原稿照合

座標群の積と逆元は原典 Levi–van der Waerden (1933) pp.155–156 に照合した。
生成交換子の引数順は原典および実装の `[aᵢ,aⱼ]` に合わせる。
積展開は、同じ内部引数順を維持する `commutator_mul_right_aux` に接続した。

座標 bijection とともに、原稿に表示された積を `normalWord` として構成した。
第一ブロックは生成元の昇順、第二ブロックは `i<j` の交換子、第三ブロックは
`i<j<k` の三重交換子で、係数は `ZMod 3` の代表値 0、1、2 を冪指数に用いる。
第二ブロックの因子は互いに可換、第三ブロックは中心にあるため、それぞれの内部列挙順は
表示の意味に影響しない。各次数の readout と cancellation でこの積の単射性を示し、
正確な有限位数から全射性を得る。`existsUnique_normalWord` は抽象的な同数性だけでなく、
この表示そのものに対する存在一意性である。

coproduct の因子単射性は原稿の retraction の証明を使い、非交和についての同型も
両向きの普遍性から構成した。群が有限であるとの追加条件はない。

モデル理論では semantic model completeness を `AllEmbeddingsElementary` として区別する。
universal theory 向けの補助定理だけで、Π₂ 理論についての Fact 2.3 や Fact 2.6 を
完成したとは扱わない。
companion と e.c. の定義は mathlib の標準 semantic universe `max u v` を用いている。
この universe の変更に関する bridge と、semantic から syntactic への逆方向は残件である。

## 検証記録

`python3 scripts/check.py` の全6 gate が同じソース状態で成功し、警告は0だった。
全12数学モジュール・504宣言を公理監査し、private名の宣言113件を含む。
391宣言の公開性も確認した。依存公理は `propext`、`Classical.choice`、`Quot.sound` のみ。

検証の入力ハッシュ、公開性と公理依存の一覧、各 gate のログを
[検証記録](audit-artifacts/2026-09-09/free-normal-form/README.md) に保存した。
対応表の `code_revision` は、数学ソースすべての SHA256 辞書を
`json.dumps(inputs, sort_keys=True)` で直列化したものの SHA256 である。
この境界の値は
`0987ef1d84e8a33728c7653ca76ef5d030ca4573f86091d87cf271f692712bec`。
Git commit や mathlib 全体の clean rebuild を意味しない。

## 残件と次の実装

Remark 2.28 の任意 rank・有限支持の正規形は未実装。
有限型上の定理をそのまま無限 rank の完成とは数えない。
中心列の一般 API、associated graded と標準 Lie API への接続へ進む。
一般 graded coproduct、同時 roots、`15n²`、生成元ベースの support、Π₂ criterion と
model companion の最終系も引き続き未完成である。
