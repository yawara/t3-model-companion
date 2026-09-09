# 実装順序と暫定見積もり

2026-09-09。対象は v4 原稿全体の paper-faithful な形式化。
旧実装の最終結論だけを移す作業とは区別する。
実装の状態は [論文対応表](../docs/paper-map.md)、設計は
[構成方針](lean-architecture.md) を参照する。

## 進める順序

| 段階 | 実装するもの | 完了を判断する数学的な境界 |
| --- | --- | --- |
| 1 | project、lint、公理検査、対応表、指数条件と基本恒等式 | 自明群を含む指数 3 条件と Fact 2.15 の項目ごとの検証 |
| 2 | 中心列、自由群、正規形、有限性 | Fact 2.27 と無限 rank の有限支持版。`t(n)` は正規形で定義 |
| 3 | associated graded、外積 Lie algebra、quotient | Proposition 2.24、2.29、Lemma 2.31。標準 Lie API と符号の一致 |
| 4 | presentation、normal closure、一般 coproduct | η₁–η₃ と自然性、任意群の strict coproduct、非自明 G と F₂ |
| 5 | 同時 roots、基底による次元評価、e.c. 転送 | Proposition 4.12 の `15n²` と内部中心列一致。ここで `f₀` を定義 |
| 6 | 共役幅、生成元ベースの support、有界非 amalgamation | Theorem 3.3 の正確な仮定・総生成元数・明示 `f(m)` |
| 7 | 一般 criterion と接続、残る例・remark、全体照合 | Corollary 3.4、および論文項目全体の形式化・fidelity 照合 |

一般モデル理論の定義・有限図式・Π₂ 理論の criterion は、段階 2–5 の群論と並行して進める。
ただし群論と一階構造の embedding の対応は早期に固定し、最後に定義の不一致を持ち込まない。
共役幅・support も、その群論的依存が揃えば段階 4–5 と並行できる。

最初の実装では、既存の自己完結した指数 3 の恒等式を必要最小限の依存で移し、
論文の各項目・符号に対応する公開定理を整える。旧 repo 自体は編集しない。
各段階を終える前に build、lint、公理検査、対応表を同じソースで通す。
主張の一部だけが完成した項目は `partial` のままにする。

2026-09-09 の検証境界では、Fact 2.15 全11項目、有限正規形と正確な位数、
自由群の普遍性、coproduct の基礎と因子単射性が完成した。
Definition 2.2 は項目 1–4 を実装した。既存の座標モデル・collecting・位数の証明を
再利用し、原稿に表示された積の存在一意性を追加している。
詳細は [有限正規形の検証記録](free-normal-form-checkpoint.md) を参照。
段階 2 の無限 rank・有限支持版と中心列の一般 API は残るため、段階全体の完了ではない。

続く同日の [無限正規形と次数商の境界](infinite-normal-form-and-graded-checkpoint.md) で、
任意 rank の有限支持正規形と中心列の一般 API・strictness を実装した。
これで段階 2 の所定の数学的境界に到達した。段階 3 は実際の中心列商、標準ZMod3 module、
graded image、誘導線形写像まで進み、Lie bracket と外積 Lie algebra の接続が次の課題となる。
モデル理論も並行してΠ₂の定義・companionモデルからe.c.モデルへの包含と、
model completeness逆bridgeに必要な有限QF diagram entailmentを証明した。

2026-09-10の [graded Lie構造の境界](graded-lie-checkpoint.md) では、実際の交換子bracket、
Lie公理・grading・誘導LieHom・次数1生成が揃った。Example 2.9の任意次元の外積Lie algebraも
実装し、自由群の実際の次数商と有限支持座標の同型を任意rankで構成した。
段階3の残りは、それらを外積targetのσ・Lie同型に接続することと一般quotientである。
モデル理論はsemantic/syntactic model completenessの完全同値、一般Π₂でmodel companionを
仮定したe.c.モデル類との一致まで進んだ。Fact 2.3逆向きなどは未完成のまま残す。

続く [外積同型・quotient・有限図式の境界](exterior-quotient-diagram-checkpoint.md) で、
任意の基底付きVへのσ₁・σ₂・σ₃と、bracket・各次数部分空間を保つLieEquivを完成した。
一般quotientのcanonical layer同型も証明し、段階3の所定の数学的境界に到達した。
段階6の共役幅3も先行して完成した。一般有限言語の有限生成図式を単一QF式で表し、
有限共通部分を固定するe.c.転送を証明した。有限図式の有限連言への圧縮と、
全QF式のT同値類の個数が有限であることは区別し、後者とFact 2.5は残件とする。
次は段階4のpresentation・graded normal closureを先に構成し、η₁–η₃へ進む。

[自由表示・同時根・一様局所有限性の境界](presentation-roots-and-uniformity-checkpoint.md) では、
任意の指定基底・代表元からのpresentationと、一般群のgraded normal closureを完成した。
Lemma 4.8の同時triple rootsも、原稿の`G × F_(3n)`の一括商で先行して実装した。
一般のblock quotientと外積の基底block分解が揃い、次の主要な境界は混合blockのtensor同型、
関係部分空間の成分計算、そこから得るcoproductのη₁–η₃と自然性である。
モデル理論はFact 2.5の全モデル共通の上界と、QF式のT同値類の有限代表集合まで進んだ。
既存のcanonical semantic universe規約の下でDefinition 2.2の6項目が完成したが、
Fact 2.3逆方向、一般criterion、companion/e.c.の他宇宙へのbridgeは残る。

[Coproduct の tensor 分解と model companion 判定の境界](coproduct-tensor-and-companion-checkpoint.md)
では、一般 Π₂ 理論の e.c. 拡大と Robinson test を旧コードから再利用・拡張し、
既存の canonical universe 規約の下で Fact 2.3 の両方向を完成した。
群論は原稿の自由 quotient presentation、normal closure の四成分の関係像、
任意次数・任意 rank の外積 tensor 同型と canonical な逆写像、free σ の因子自然性まで進んだ。
η₁ は実際の同型、η₂・η₃ は canonical な写像と自然性を持つ。
次は関係像の tensor block への輸送・商の分解から η₂・η₃ の全単射性を証明する。
block 間 bracket、strict coproduct、F₂、同時 commutator roots、次元評価と
一般 bounded-amalgamation criterion は残る。段階4全体の完了とはしない。
この境界では53モジュール・1,789宣言の全検査が警告0で通過した。
モデル理論側は [Fact 2.6 の実装境界](bounded-amalgamation-implementation-frontier.md) に
一般の必要方向・十分方向の signature と再利用先を記録した。

[Graded coproduct と一般 amalgamation 判定の境界](graded-coproduct-and-amalgamation-checkpoint.md)
では、原稿の自由商表示と符号付き外積を通じて η₂・η₃の全単射性を証明し、
block bracket 包含、任意群の strict coproduct、非自明 G と F₂ の中心列一致を完成した。
これで段階4の所定の数学的境界に到達した。
一般モデル理論は Fact 2.6 の両方向と、実際の T₃ の Π₂・局所有限性の接続まで進んだ。
段階5では同時 derived relator の normal word 表示と生成元数による第一・第二層の次元評価が
できたが、同時交換子 roots の単射性と strictification・e.c. 転送・15n² は未完成である。
主定理の bounded obstruction を仮定する model companion への橋は、無条件の存在とは区別する。

[同時交換子 roots・e.c. 群・support の境界](commutator-roots-and-support-checkpoint.md) では、
原稿の同時 quotient と Claim A–C により Lemma 4.6 を完成した。
具体的な roots と F₂ の分離から有限図式で witness を戻し、Proposition 4.11 の3結論も得た。
段階6では、旧コードの全要素列挙を生成列に拡張し、Lemma 3.2 の正確な `3(m+1)n` と
H₀内部の normal-closure certificate を完成した。
次は段階5の二段階 strictification と `15n²` envelope を組み立て、群論的 amalgamation
表示と主定理の明示 bound へ接続する。

[基底による二段階 strictification の境界](strictification-checkpoint.md) では、
実際の graded kernel の基底を群の元へ持ち上げ、欠損の生成等式を証明した。
同時交換子商で Lemma 4.7 の `2m`、同時三重交換子商で Lemma 4.9 の
`3 * binom(m,2)` を得る。次は二段階の拡大に F₂ を付け、有限図式で e.c. 群へ戻すことで
段階5の終端 Proposition 4.12 の `15n²` と内部中心列一致を完成する。

## どこに時間がかかるか

現在の監査から言えるのは、既存 Lean の終端までに 66 モジュール・約 1.8 万行がある一方、
v4 の一般 graded coproduct、F₂、同時 roots、次元評価、一般 criterion の一部は新規作業ということ。
既存コードの行数から v4 の完成率や所要時間を直接計算することはできない。

集中して継続する場合、**全体は数週間〜数か月、初期の計画幅としては 1〜3 か月程度**を
見込む。これは新 project での実装速度をまだ測定していない段階の粗い見積もりである。
数学的 API の作り直しが必要になれば、この幅を超える可能性もある。

作業量の内訳としては次の幅を想定する。並行する部分があるため、単純な合計を日程とはしない。

| 作業 | 暫定的な規模感 |
| --- | --- |
| 雛形と最初の基礎証明 | 数時間〜数日 |
| 既存の基礎・正規形の移植と整理 | 数日〜1週間程度 |
| associated graded・外積・一般 coproduct | 数週間。最も不確実な部分 |
| 同時 roots・次元評価・`15n²` | 1〜数週間 |
| 一般モデル理論・終端接続 | 1〜数週間。群論と並行 |
| 残項目・全体の原稿照合と検査 | 数日〜1週間程度 |

最初に見積もりを更新するのは、正規形の再利用範囲と associated graded の基本 API が
実際にコンパイルできた時点。次は Proposition 4.3 の η₁–η₃ と自然性が揃った時点とする。
計測するのは、実装時間、未解決の数学的境界、再利用できた証明、API 変更による手戻りであり、
空ファイル数や `planned` の宣言予定数は進捗に数えない。
