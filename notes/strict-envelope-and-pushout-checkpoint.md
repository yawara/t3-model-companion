# Strict envelope と amalgam の商表示の検証境界

> Historical T3 revision identifiers have been omitted for publication. Recorded commands, outcomes, and source hashes describe the original checks; this edited record does not certify the rewritten historical snapshots.

2026-09-10。Proposition 4.12、Proposition A と主定理の商表示を対象とする。
原稿 SHA256 は
`79745dfa1660a827c51ec3c6b2006ee9d6243cb4702f97a75e5b55357b89f50b`。
87モジュールの全体検査が終了コード0・警告0で通過した。
全論文の goal は継続中であり、Theorem 3.3 と無条件の model companion の存在は未完成である。

## 固定した検証結果

`python3 scripts/check.py` の build、import 集約、environment lint、text lint、公理監査、
論文対応検査の全6段階が通過した。検査中の入力不変性と保存時の live SHA256 一致を確認した。
これは pin 済み Lean/mathlib キャッシュを使ったローカル検証であり、mathlib 自体の
クリーンビルドや CI の実行ではない。

87モジュール・2,590宣言を監査した。対応表は50項目・75部分項目で、
43 proved・4 partial・3 planned。項目の集計は作業量に対する完成率を意味しない。
private-name 宣言481、public-name 宣言2,109で後者はすべて exported。
exported な監査対象名は2,125であり、private-name の生成補題16個と重複する。
公理依存は `propext`、`Classical.choice`、`Quot.sound` のみである。
全入力・全宣言・各検査ログを [保存成果物](audit-artifacts/2026-09-10/strict-envelope-pushout/README.md)
に固定した。数学ソース revision は
`74f7ca9dd544ffce1448cd86f75c50d9d379d721b2823d6ec23403fd845b6d6c`。
これは `T3.lean` と `T3/**/*.lean` の path-to-SHA256 辞書を `sort_keys=True` で JSON 化した
ものの SHA256 である。

## Proposition 4.12 と Proposition A

`T3/ModelTheory/StrictEnvelope.lean` は数値関数 `strictEnvelopeBound n = 15*n^2` を定義し、
論文通り二段階の同時 strictification を経て `D₃ = D₂ ∐ F₂` を作る。
第一段階の交叉等式を包含写像の逆像として書き直し、第二段階へ渡す。
`D₂` は strict なので `D₃ → H₂ ∐ F₂` は単射である。
`C ≠ 1` の場合、拡大への単射を通じて `D₂ ≠ 1` を証明し、Lemma 4.5 を適用する。
非自明性を単に仮定として追加していない。

生成元数は順に `3n`、`3n + 3*choose(3n,2)`、それに2を加えた値である。
最後の値が `15n²` 以下となるのは `n ≥ 1` の場合であり、`C ≠ 1` と `rank C ≤ n` から
この条件を得る。`C = 1` は `D = C` として独立に処理し、`n = 0` も含む。
補助モジュール `Coproduct/Generation` は両因子の像による生成を証明し、
有限生成性と `rank(G ∐ H) ≤ rank G + rank H` を供給する。
これは実際の cube quotient に対する定理で、因子の指数条件を仮定しない。

有限生成指数3群の有限性を自由群の有限性から供給する。
`ExistentiallyClosedGroups.exists_group_embedding` の共通パラメータ型を有限群 C 全体とし、
`D₃` を M に戻す embedding が C の全要素を固定することを証明する。
返る D はその embedding の range であり、包含 `C ≤ D`、rank 上界、内部中心列一致を持つ。
内部中心列一致の群同型による輸送と Lemma 2.26 から最終的な strictness を得る。
Proposition A はさらに `∃ f₀, ∀ n M C, ...` を明示し、全モデルに一つの関数を使うことを示す。

代数的拡大 `exists_centralSeries_extension` は任意の宇宙の G を扱い、拡大を同じ宇宙に作る。
e.c. の結論は既存の canonical semantic universe `M : Type` を継承する。
この制限と一般モデル宇宙への bridge の未完成は対応表にも記録している。
数学的構成・固定するパラメータ・零の場合を独立担当が照合した。

## 主定理の商表示

`T3/GroupTheory/Amalgamation.lean` は二つの準同型 `f : A → G`、`g : A → H` に対して
`δ(a)=inl(f a)*(inr(g a))⁻¹` とその実際の normal closure を定義する。
`Pushout f g` は coproduct をこの normal closure で割った商である。
任意の宇宙の指数3群への普遍写像・左右の可換三角形・一意性を証明する。
因子への入力写像の単射性や有限性はこの構成には不要である。

通常の amalgam の存在は両因子からこの商への自然写像が単射であることと同値である。
像の交わりがちょうど A になる条件は加えていない。
`AmalgamableOver` の target は因子の宇宙の最大値を使うが、任意の大きな target の
amalgam からもこの canonical 商の単射性を導けるので、宇宙制限により障害を捏造しない。

amalgam が存在しない場合、左または右の因子の非自明元が関係部分群に入る。
さらに、A の任意の生成族に対応する relators の normal closure が全 relators の
normal closure と等しいことを証明する。商への二つの準同型が生成族上で一致するため、
A 全体で一致するという原稿の省略を展開した。生成族の添字の有限性は不要である。
旧 `ExponentThree/PushoutWitness.lean` の証人の取り出しを再利用し、実際の canonical
coproduct と論文の左右・符号に合わせた。

これで Theorem 3.3 の冒頭の quotient criterion と両方の証人を供給するが、
有限部分群 D での非 amalgamation はまだ得ていない。対応表は主定理を partial のまま保つ。

## 次の数学的境界

1. `rank A ≤ log₃|A| ≤ log₃|B| ≤ t(m)` を正確な位数・冪の不等式で接続する。
   B の生成元数だけによる上界を保ち、位数依存の旧 bound で代用しない。
2. Lemma 3.2 の support を M に引き戻し、A と必要なら左の証人を加えて
   `rank C ≤ (3m+4)t(m)+1` を得る。
3. strict envelope を適用し、`D ∐ B → M ∐ B` の単射性を使って、実際の小さい H₀ 内の
   normal-closure 証明を D の coproduct 内に引き戻す。左/右双方の証人を扱う。
4. 群論的 amalgam と一階構造の amalgam を接続し、一般の Fact 2.6 へ無条件の bound を渡す。

主定理以外にも Definition 2.7、Remark 2.8、共有 triple roots、記法と残る例、
一般モデル宇宙への bridge が残る。以前の84モジュールの境界は
[二段階 strictification](strictification-checkpoint.md)、コミット `[historical revision omitted]` に固定したまま保持する。
