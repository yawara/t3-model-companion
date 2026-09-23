# v7 原稿への移行と出典照合

> 履歴資料（v7 原稿）。原稿と PDF は [archives](../archives/README.md) に保存。現行版への移行は [v8 移行記録](v8-migration.md) を参照。

2026-09-22。現行原稿を [T3_modelcompanion_v7.tex](../archives/T3_modelcompanion_v7.tex) とする。
SHA256 は `fb32d367e325f081eaeaf77b0c680662c9f58d1e8bc2a45adb0436cbe17c3ad6`。
原稿本文は変更していない。

旧 [T3_modelcompanion_v4.tex](../archives/T3_modelcompanion_v4.tex) と
[PDF](../archives/T3_modelcompanion_v4.pdf) は `archives/` へ移した。
両ファイルの内容が移動前の Git HEAD と byte 単位で同一であることを確認した。
旧TeXの SHA256 は `79745dfa1660a827c51ec3c6b2006ee9d6243cb4702f97a75e5b55357b89f50b`。

## 既存の数学的内容

旧稿の47個の番号付き項目、Proposition A、無番号定義2個をすべて新稿と照合した。
§2・§3の表示番号は変わらない。新しい Remark 4.2 により、旧4.2–4.12は4.3–4.13へ移る。
以下の8つの番号付きstatementだけに文字列差分があり、いずれも数学的な仮定・結論・
量化範囲・数値評価を変更していない。

- Definition 2.2: “quantifier-free” のハイフン。
- Fact 2.6: “don't” から “do not” への表記。
- Proposition 2.11: “a vector space” の冠詞。
- Remark 2.28: “from the identity” への英文修正。
- Theorem 3.3: “groups” / “amalgam” の表記、末尾の不要な “element” の削除。
- Corollary 3.4: “groups” の冠詞。
- 旧 Proposition 4.3 = v7 Proposition 4.4: “natural maps induced by” への表記。
- 旧 Lemma 4.5 = v7 Lemma 4.6: rank 2 の relatively free group in V₃ と明示。

残る40個の番号付き・特別番号statementは同一の本文である。
§2–§4の証明差分も読み、英文修正、e.c. 群のroot構成の既存補題への参照明示、
strict envelope の自明な入力に `D=1` を明示した変更であることを確認した。
`3(m+1)n`、`15n²`、`f(m)=15((3m+4)t(m)+1)²` と主要構成は変わらない。
既存Leanの符号化・省略補充の評価は [旧完成記録](paper-faithful-completion.md) と
[旧toolchain移行記録](lean-mathlib-4-33-1-upgrade.md) に残す。

新しい Remark 4.2 (`remark:G=H`, 879–881行) は、§4の指数3群という文脈で、
既存 `T3.eq_top_of_sup_commutator_eq_top` の結論と一致する。
一般の群すべてに指数条件なしで成立する、と解釈していない。

## 新たに追跡する項目

v7には55個の番号付き項目とProposition Aがある。無番号定義2個、§6のBurnside群による
還元、Takeuchi予想を加え、対応表は60項目・80部分項目を登録する。

| 出典 | 安定ID | 内容 |
| --- | --- | --- |
| Remark 4.2, 879–881 | `structure.generation_mod_derived` | abelianizationを覆う部分群は全体 |
| Example 5.1, 1346–1359 | `examples.non_strict_coproduct` | B(3,3)内の具体的な非strict部分群と非amalgamation |
| Remark 5.2, 1361–1367 | `examples.strictness_necessity` | coproduct比較でstrictnessを省けない |
| Lemma 5.3, 1373–1377 | `examples.commutator_rank_lower_bound` | aₙ∈γ₂(D)ならd(D)≥2n |
| Lemma 5.4, 1411–1415 | `examples.cyclic_amalgamation` | 巡回基底上のamalgamationの同値条件 |
| Proposition 5.5, 1438–1444 | `examples.unbounded_witness_rank` | e.c.仮定なしの二つの生成元数下界 |
| Question 6.1, 1482–1485 | `questions.locally_finite_varieties` | 局所有限な群varietyのmodel companion |
| Question 6.2, 1507–1511 | `questions.bounded_exponent_varieties` | 有界指数と逆方向 |
| §6本文, 1519–1525 | `questions.burnside_local_finiteness` | 全有限rank Burnside群の有限性による還元 |
| §6予想, 1527–1530; §1, 151–154 | `questions.takeuchi_conjecture` | Takeuchi予想の二つの表現 |

§5は原稿の具体的な構成・任意部分群という範囲・係数体F₃・下界2nを維持する。
新項目の証明済み状態はそれぞれの公開宣言と統合検査に依存し、出典登録だけで完了としない。
§6の質問2件とTakeuchi予想は `open` とし、証明予定のstubやproject axiomを作らない。
原稿1537–1541行の大素数に関する別論文予告は、このリポジトリの証明済み結果ではない。
§6の検討は [第6節の考察](section-six-analysis.md) に記す。

## 出典移動表

下表は既存の50項目を安定IDで対応させる。個々のenumerated partのsource_lineもv7へ移した。

| 安定ID | v4項目 | v4行 | v7項目 | v7行 |
| --- | --- | --- | --- | --- |
| `preliminaries.exponent_three` | prose 2.preamble | 136–142 | prose 2.preamble | 215–221 |
| `preliminaries.notation` | notation 2.1 | 145–172 | notation 2.1 | 224–251 |
| `model_theory.basic_definitions` | definition 2.2 | 178–193 | definition 2.2 | 257–272 |
| `model_theory.companion_iff_ec` | fact 2.3 | 195–201 | fact 2.3 | 274–280 |
| `model_theory.local_finiteness` | definition 2.4 | 203–206 | definition 2.4 | 282–285 |
| `model_theory.uniform_local_finiteness` | fact 2.5 | 209–212 | fact 2.5 | 288–291 |
| `model_theory.bounded_amalgamation_criterion` | fact 2.6 | 214–228 | fact 2.6 | 293–307 |
| `linear_algebra.graded_lie` | definition 2.7 | 267–279 | definition 2.7 | 346–358 |
| `linear_algebra.degree_one_generation` | remark 2.8 | 281–287 | remark 2.8 | 360–366 |
| `linear_algebra.truncated_exterior` | example 2.9 | 289–306 | example 2.9 | 368–385 |
| `linear_algebra.block_homogeneous` | definition 2.10 | 308–312 | definition 2.10 | 387–391 |
| `linear_algebra.block_quotient` | proposition 2.11 | 314–317 | proposition 2.11 | 393–396 |
| `preliminaries.set_commutator` | prose 2.group_preamble | 324–325 | prose 2.group_preamble | 403–404 |
| `preliminaries.central_series` | definition 2.12 | 326–339 | definition 2.12 | 405–418 |
| `preliminaries.upper_central_recursive` | remark 2.13 | 340–342 | remark 2.13 | 419–421 |
| `preliminaries.central_series_properties` | fact 2.14 | 344–349 | fact 2.14 | 423–428 |
| `preliminaries.elementary_identities` | fact 2.15 | 355–371 | fact 2.15 | 434–450 |
| `preliminaries.free_coproduct` | fact 2.16 | 374–376 | fact 2.16 | 453–455 |
| `preliminaries.coproduct_factor_injective` | lemma 2.17 | 378–382 | lemma 2.17 | 457–461 |
| `preliminaries.associated_graded` | definition 2.18 | 391–408 | definition 2.18 | 470–487 |
| `preliminaries.associated_graded_properties` | lemma 2.19 | 411–420 | lemma 2.19 | 490–499 |
| `preliminaries.graded_image` | notation 2.20 | 422–437 | notation 2.20 | 501–516 |
| `preliminaries.associated_graded_examples` | example 2.21 | 439–445 | example 2.21 | 518–524 |
| `preliminaries.associated_graded_map` | definition 2.22 | 449–456 | definition 2.22 | 528–535 |
| `preliminaries.lcs_strictness` | definition 2.23 | 460–468 | definition 2.23 | 539–547 |
| `preliminaries.graded_injectivity_strictness` | proposition 2.24 | 470–480 | proposition 2.24 | 549–559 |
| `preliminaries.central_series_coincide` | definition 2.25 | 503–508 | definition 2.25 | 582–587 |
| `preliminaries.strict_of_internal` | lemma 2.26 | 510–517 | lemma 2.26 | 589–596 |
| `preliminaries.finite_normal_form` | fact 2.27 | 525–533 | fact 2.27 | 604–612 |
| `preliminaries.infinite_normal_form` | remark 2.28 | 535–545 | remark 2.28 | 614–624 |
| `preliminaries.free_graded_equiv` | proposition 2.29 | 550–570 | proposition 2.29 | 629–649 |
| `preliminaries.infinite_free_graded` | remark 2.30 | 600–602 | remark 2.30 | 679–681 |
| `preliminaries.graded_quotient` | lemma 2.31 | 623–626 | lemma 2.31 | 702–705 |
| `main.conjugate_width` | proposition 3.1 | 653–659 | proposition 3.1 | 731–737 |
| `main.bounded_support` | lemma 3.2 | 668–677 | lemma 3.2 | 746–755 |
| `main.proposition_a` | customproposition A | 697–699 | customproposition A | 775–777 |
| `main.bounded_witness` | theorem 3.3 | 702–712 | theorem 3.3 | 780–790 |
| `main.model_companion` | corollary 3.4 | 743–745 | corollary 3.4 | 821–823 |
| `structure.basis_lift` | proposition 4.1 | 759–763 | proposition 4.1 | 837–841 |
| `structure.normal_closure_graded` | lemma 4.2 | 802–811 | lemma 4.3 | 883–892 |
| `structure.graded_coproduct` | proposition 4.3 | 843–864 | proposition 4.4 | 924–945 |
| `structure.strict_coproduct` | lemma 4.4 | 946–951 | lemma 4.5 | 1027–1032 |
| `structure.free_two_stabilization` | lemma 4.5 | 962–967 | lemma 4.6 | 1043–1048 |
| `structure.simultaneous_commutator_roots` | lemma 4.6 | 1010–1017 | lemma 4.7 | 1091–1098 |
| `structure.derived_strictification` | lemma 4.7 | 1076–1082 | lemma 4.8 | 1157–1163 |
| `structure.simultaneous_triple_roots` | lemma 4.8 | 1110–1117 | lemma 4.9 | 1191–1198 |
| `structure.lcs_strictification` | lemma 4.9 | 1133–1141 | lemma 4.10 | 1214–1222 |
| `structure.shared_triple_roots` | remark 4.10 | 1177–1182 | remark 4.11 | 1258–1263 |
| `structure.ec_central_series` | proposition 4.11 | 1185–1195 | proposition 4.12 | 1266–1276 |
| `structure.strict_envelope` | proposition 4.12 | 1212–1220 | proposition 4.13 | 1293–1301 |

## メタデータと検証の境界

`AGENTS.md`、README、構成方針、現行fidelity案内、`formalization.yaml`、Palomar案内、
`Challenge.lean`、`Solution.lean`、全既存数学モジュールのdocstring、対応表、チェック入力を
v7へ移した。旧検証記録には履歴である旨とarchiveへの案内を加え、本文の当時の行・番号・
hash・検証結果は維持する。`notes/audit-artifacts/` の固定成果物は変更しない。

出典移行時に既存110 Leanファイルのコメント以外のtoken列がGit HEADと不変であることを
確認した。source locatorの更新自体は数学的なLean statementやproof bodyを変更していない。
既存の `proved` / `proof_checked` は上記の数学的同一性に基づき引き継ぎ、旧機械検証の
revisionはその時点のまま記録した。新しい統合検査を実施する前に成功を主張しない。

移行担当の検査範囲は `python3 scripts/paper_map.py --check` と
`python3 scripts/check_palomar_metadata.py`、archiveのbyte一致、旧Leanのtoken不変性、
現行ファイルに旧出典が残っていないことの静的確認である。
`python3 scripts/check.py` の全体検査および新規数学ファイルの検査結果は、統合後の記録に従う。
新しい証明の範囲と統合後の検証結果は [v7形式化記録](v7-formalization.md) にまとめる。
