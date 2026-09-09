# 論文と Lean の対応表

このファイルは `docs/paper-map.toml` から生成する。変更後は `python3 scripts/paper_map.py --write`、整合性検査は `--check` を使う。

対象: [T3_modelcompanion_v4.tex](../T3_modelcompanion_v4.tex)。SHA256: `79745dfa1660a827c51ec3c6b2006ee9d6243cb4702f97a75e5b55357b89f50b`。

番号付き 47 項目、Proposition A、§2 冒頭の指数条件、および集合の交換子部分群を個別登録する。行・表示番号は補助情報で、安定 ID を主キーとする。

項目全体の状態: `planned` 3, `partial` 2, `stated` 0, `proved` 45。

`formalization` と `fidelity` は別々に記録する。`partial` は項目の一部だけに実在宣言がある状態、`stated` は型・定義の記述まで、`proved` は別の検証記録を伴う完成状態を表す。`unchecked` / `statement_checked` / `proof_checked` は原稿との照合状況である。

このスクリプトは TeX の網羅性、モジュールと宣言の字句上の所在、表示の整合性を検査する。Lean の elaboration・公理依存・lint・数学的 faithful 性は別途検証する。予定名は実在宣言ではなく、未着手の項目のために Lean stub を作らない。

| 論文項目 / 安定 ID | 内容 | 原文 label / 行 | 公開モジュール（予定を含む） | formalization | fidelity |
| --- | --- | --- | --- | --- | --- |
| §2 冒頭<br>`preliminaries.exponent_three` | 指数は 3 を割る条件を用い、自明群を含める | label なし<br>136–142 | `T3.GroupTheory.Basic`<br>`T3.ModelTheory.GroupLanguage`<br>`T3.ModelTheory.ExponentThree` | proved | proof_checked |
| Notation 2.1<br>`preliminaries.notation` | 群の記法、生成元数、自由指数群、coproduct | label なし<br>145–172 | `T3.GroupTheory.Basic`<br>`T3.GroupTheory.Free.Basic`<br>`T3.GroupTheory.Coproduct.Basic`<br>`T3.GroupTheory.CentralSeries`<br>`T3.GroupTheory.GeneratorRank`<br>`T3.ModelTheory.ExponentThree` | partial | unchecked |
| Definition 2.2<br>`model_theory.basic_definitions` | companion、model completeness、e.c.、Π₂、有限図式 | label なし<br>178–193 | `T3.ModelTheory.ModelCompanion`<br>`T3.ModelTheory.Inductive`<br>`T3.ModelTheory.FiniteDiagram`<br>`T3.ModelTheory.ModelCompleteness`<br>`T3.ModelTheory.LocallyFinite`<br>`T3.ModelTheory.UniformLocalFiniteness` | proved | proof_checked |
| Fact 2.3<br>`model_theory.companion_iff_ec` | Π₂ 理論の model companion と e.c. class の一致 | label なし<br>195–201 | `T3.ModelTheory.Inductive`<br>`T3.ModelTheory.PiTwoDirectLimit`<br>`T3.ModelTheory.ExistentiallyClosedExtension`<br>`T3.ModelTheory.ElementaryChain`<br>`T3.ModelTheory.RobinsonTest`<br>`T3.ModelTheory.ModelCompanionCriterion` | proved | proof_checked |
| Definition 2.4<br>`model_theory.local_finiteness` | 理論の局所有限性 | label なし<br>203–206 | `T3.ModelTheory.LocallyFinite` | proved | proof_checked |
| Fact 2.5<br>`model_theory.uniform_local_finiteness` | 有限言語における一様な生成部分構造の位数評価 | label なし<br>209–212 | `T3.ModelTheory.LocallyFinite`<br>`T3.ModelTheory.UniformLocalFiniteness` | proved | proof_checked |
| Fact 2.6<br>`model_theory.bounded_amalgamation_criterion` | model companion の存在と有界非 amalgamation 障害の同値 | `fact:locally finiteness and model companion`<br>214–228 | `T3.ModelTheory.ExistentialWitness`<br>`T3.ModelTheory.Amalgamation`<br>`T3.ModelTheory.BoundedAmalgamation`<br>`T3.ModelTheory.FiniteObstructions`<br>`T3.ModelTheory.ExtensionAxioms`<br>`T3.ModelTheory.BoundedAmalgamationCriterion` | proved | proof_checked |
| Definition 2.7<br>`linear_algebra.graded_lie` | graded Lie ring と graded Lie algebra | label なし<br>267–279 | `T3.LinearAlgebra.GradedLie` | planned | unchecked |
| Remark 2.8<br>`linear_algebra.degree_one_generation` | 反対称性と次数 1 からの生成の特徴づけ | label なし<br>281–287 | `T3.LinearAlgebra.GradedLie` | planned | unchecked |
| Example 2.9<br>`linear_algebra.truncated_exterior` | 次数 1–3 の外冪と符号付き Lie bracket | `example:Grassmann algebra`<br>289–306 | `T3.LinearAlgebra.Wedge`<br>`T3.LinearAlgebra.TruncatedExterior` | proved | proof_checked |
| Definition 2.10<br>`linear_algebra.block_homogeneous` | block-homogeneous subspace | label なし<br>308–312 | `T3.LinearAlgebra.BlockDecomposition` | proved | proof_checked |
| Proposition 2.11<br>`linear_algebra.block_quotient` | block-homogeneous quotient の直和分解 | label なし<br>314–317 | `T3.LinearAlgebra.BlockDecomposition` | proved | proof_checked |
| §2 群論の無番号定義<br>`preliminaries.set_commutator` | 任意の二つの集合の交換子が生成する部分群 | label なし<br>324–325 | `T3.GroupTheory.Basic` | proved | proof_checked |
| Definition 2.12<br>`preliminaries.central_series` | 下部中心列と上部中心列 | label なし<br>326–339 | `T3.GroupTheory.CentralSeries` | proved | proof_checked |
| Remark 2.13<br>`preliminaries.upper_central_recursive` | 上部中心列の反復交換子による定義と再帰的定義の同値 | label なし<br>340–342 | `T3.GroupTheory.CentralSeries` | proved | proof_checked |
| Fact 2.14<br>`preliminaries.central_series_properties` | 中心列の交換子評価と nilpotent 群の上下中心列の包含 | label なし<br>344–349 | `T3.GroupTheory.CentralSeries` | proved | proof_checked |
| Fact 2.15<br>`preliminaries.elementary_identities` | 指数 3 群の基本恒等式 11 項目 | `fact:elementary equations`<br>355–371 | `T3.GroupTheory.Identities`<br>`T3.GroupTheory.Free.Examples` | proved | proof_checked |
| Fact 2.16<br>`preliminaries.free_coproduct` | 生成集合の非交和の自由群と coproduct | label なし<br>374–376 | `T3.GroupTheory.Coproduct.Basic` | proved | proof_checked |
| Lemma 2.17<br>`preliminaries.coproduct_factor_injective` | coproduct の因子写像の単射性 | label なし<br>378–382 | `T3.GroupTheory.Coproduct.Basic` | proved | proof_checked |
| Definition 2.18<br>`preliminaries.associated_graded` | 群の associated graded Lie algebra | label なし<br>391–408 | `T3.GroupTheory.AssociatedGraded`<br>`T3.GroupTheory.AssociatedGraded.Bracket`<br>`T3.GroupTheory.AssociatedGraded.Lie` | proved | proof_checked |
| Lemma 2.19<br>`preliminaries.associated_graded_properties` | 次数 4 の消滅、三重 bracket 恒等式、次数 1 による生成 | label なし<br>411–420 | `T3.GroupTheory.AssociatedGraded`<br>`T3.GroupTheory.AssociatedGraded.Bracket`<br>`T3.GroupTheory.AssociatedGraded.Lie`<br>`T3.GroupTheory.AssociatedGraded.Generation` | proved | proof_checked |
| Notation 2.20<br>`preliminaries.graded_image` | 元の初期成分と部分群の graded image | label なし<br>422–437 | `T3.GroupTheory.AssociatedGraded` | proved | proof_checked |
| Example 2.21<br>`preliminaries.associated_graded_examples` | 可換群・直積・2 生成自由群の graded | label なし<br>439–445 | `T3.GroupTheory.AssociatedGradedExamples`<br>`T3.GroupTheory.AssociatedGraded.Product` | partial | unchecked |
| Definition 2.22<br>`preliminaries.associated_graded_map` | 準同型が誘導する gr(f) | label なし<br>449–456 | `T3.GroupTheory.AssociatedGraded`<br>`T3.GroupTheory.AssociatedGraded.Bracket`<br>`T3.GroupTheory.AssociatedGraded.Lie` | proved | proof_checked |
| Definition 2.23<br>`preliminaries.lcs_strictness` | lower-central strict inclusion | label なし<br>460–468 | `T3.GroupTheory.CentralSeries` | proved | proof_checked |
| Proposition 2.24<br>`preliminaries.graded_injectivity_strictness` | gr(f) の単射性、f の単射性、strictness | `proposition:gr(f) and LCS`<br>470–480 | `T3.GroupTheory.AssociatedGraded`<br>`T3.GroupTheory.AssociatedGraded.Lie` | proved | proof_checked |
| Definition 2.25<br>`preliminaries.central_series_coincide` | 上下中心列が逆順に一致する条件 | label なし<br>503–508 | `T3.GroupTheory.CentralSeries` | proved | proof_checked |
| Lemma 2.26<br>`preliminaries.strict_of_internal` | 内部中心列一致から任意 ambient における strictness | label なし<br>510–517 | `T3.GroupTheory.CentralSeries` | proved | proof_checked |
| Fact 2.27<br>`preliminaries.finite_normal_form` | Levi–van der Waerden の有限 rank 正規形と位数 | `fact:Levi and van der Waerden`<br>525–533 | `T3.GroupTheory.Free.Basic`<br>`T3.GroupTheory.Free.Model`<br>`T3.GroupTheory.Free.ModelComparison`<br>`T3.GroupTheory.Free.Collection`<br>`T3.GroupTheory.Free.NormalForm` | proved | proof_checked |
| Remark 2.28<br>`preliminaries.infinite_normal_form` | 任意 rank の有限支持正規形 | `remark:infinite dim`<br>535–545 | `T3.GroupTheory.Free.FiniteSupport`<br>`T3.GroupTheory.Free.InfiniteNormalForm` | proved | proof_checked |
| Proposition 2.29<br>`preliminaries.free_graded_equiv` | 自由指数 3 群の associated graded と truncated exterior Lie algebra | `proposition:gr(F) is Grassmann algebra`<br>550–570 | `T3.GroupTheory.Free.Graded`<br>`T3.GroupTheory.Free.Exterior`<br>`T3.GroupTheory.Free.ExteriorBracket`<br>`T3.GroupTheory.Free.ExteriorLie` | proved | proof_checked |
| Remark 2.30<br>`preliminaries.infinite_free_graded` | 無限 rank の graded 同型 | label なし<br>600–602 | `T3.GroupTheory.Free.Exterior`<br>`T3.GroupTheory.Free.ExteriorLie` | proved | proof_checked |
| Lemma 2.31<br>`preliminaries.graded_quotient` | quotient の associated graded | `lemma:gr of quotient`<br>623–626 | `T3.GroupTheory.GradedQuotient` | proved | proof_checked |
| Proposition 3.1<br>`main.conjugate_width` | principal normal closure の共役幅 3 | `proposition:bounded number of conjugates`<br>653–659 | `T3.GroupTheory.ConjugateWidth` | proved | proof_checked |
| Lemma 3.2<br>`main.bounded_support` | 生成元数による support bound 3(m+1)n | `lemma:witness in bdd support`<br>668–677 | `T3.GroupTheory.Support`<br>`T3.GroupTheory.Support.Collection`<br>`T3.GroupTheory.Support.Conjugator` | proved | proof_checked |
| Proposition A<br>`main.proposition_a` | 一様に有界な LCS strict envelope の存在 | label なし<br>697–699 | `T3.ModelTheory.StrictEnvelope` | proved | proof_checked |
| Theorem 3.3<br>`main.bounded_witness` | B の生成元数のみによる非 amalgamation 障害の総生成元数評価 | `thm:main`<br>702–712 | `T3.Main.BoundedWitness`<br>`T3.GroupTheory.Amalgamation`<br>`T3.GroupTheory.GeneratorRank.Cardinality`<br>`T3.GroupTheory.Coproduct.Support`<br>`T3.GroupTheory.Support.Transport` | proved | proof_checked |
| Corollary 3.4<br>`main.model_companion` | 指数 3 群の理論は model companion をもつ | label なし<br>743–745 | `T3.Main.ModelCompanion`<br>`T3.ModelTheory.ExponentThree`<br>`T3.ModelTheory.GroupAmalgamation` | proved | proof_checked |
| Proposition 4.1<br>`structure.basis_lift` | abelianization の基底 lift による全射自由表示 | `proposition:lift`<br>759–763 | `T3.GroupTheory.Generation`<br>`T3.GroupTheory.Presentation` | proved | proof_checked |
| Lemma 4.2<br>`structure.normal_closure_graded` | derived 内の normal closure とその graded image | `lemma:gr of normal closure`<br>802–811 | `T3.GroupTheory.GradedNormalClosure` | proved | proof_checked |
| Proposition 4.3<br>`structure.graded_coproduct` | coproduct の η₁–η₃、tensor block 分解と bracket | `proposition:gr of free product`<br>843–864 | `T3.GroupTheory.Coproduct.Graded`<br>`T3.GroupTheory.Coproduct.Presentation`<br>`T3.GroupTheory.Coproduct.Relations`<br>`T3.GroupTheory.AssociatedGraded.Subgroup`<br>`T3.GroupTheory.Free.ExteriorNaturality`<br>`T3.LinearAlgebra.ExteriorSum`<br>`T3.LinearAlgebra.ExteriorTensor`<br>`T3.ForMathlib.PowersetCardSum`<br>`T3.LinearAlgebra.ExteriorLowDegree`<br>`T3.GroupTheory.Coproduct.FreeGraded`<br>`T3.GroupTheory.Coproduct.QuotientMaps`<br>`T3.GroupTheory.Coproduct.GradedEquiv`<br>`T3.GroupTheory.Coproduct.BlockBracket`<br>`T3.GroupTheory.GradedQuotient`<br>`T3.ForMathlib.LinearMapQuotient` | proved | proof_checked |
| Lemma 4.4<br>`structure.strict_coproduct` | strict inclusion が coproduct の単射性を保存する | `lemma:free-product-amalgam`<br>946–951 | `T3.GroupTheory.Coproduct.Strict` | proved | proof_checked |
| Lemma 4.5<br>`structure.free_two_stabilization` | 非自明群と F₂ の coproduct の strictness と内部中心列一致 | `lemma:coincidence of central series`<br>962–967 | `T3.GroupTheory.Coproduct.CentralSeries`<br>`T3.GroupTheory.Coproduct.CentralSeriesCriterion`<br>`T3.GroupTheory.Coproduct.FreeTwoSeparation`<br>`T3.GroupTheory.Coproduct.FreeTwo`<br>`T3.ForMathlib.TensorProduct` | proved | proof_checked |
| Lemma 4.6<br>`structure.simultaneous_commutator_roots` | G * F₂ₙ の quotient における同時 commutator roots と単射性 | `lemma:basic commutator root`<br>1010–1017 | `T3.GroupTheory.Roots.Commutator`<br>`T3.GroupTheory.Roots.CommutatorRelations` | proved | proof_checked |
| Lemma 4.7<br>`structure.derived_strictification` | 高々 2m 元を付加する derived strictification | `lemma:commutator root`<br>1076–1082 | `T3.GroupTheory.Roots.DerivedStrictification`<br>`T3.GroupTheory.Roots.DefectBasis`<br>`T3.GroupTheory.GeneratorRank`<br>`T3.ForMathlib.Subgroup` | proved | proof_checked |
| Lemma 4.8<br>`structure.simultaneous_triple_roots` | G × F₃ₙ の quotient における同時 triple roots と単射性 | `lemma:triple commutator root`<br>1110–1117 | `T3.GroupTheory.Roots.Triple` | proved | proof_checked |
| Lemma 4.9<br>`structure.lcs_strictification` | 高々 3·binom(n,2) 元を付加する γ₃ strictification | `lemma:number of generators for triple commutator roots`<br>1133–1141 | `T3.GroupTheory.Roots.LowerCentralStrictification`<br>`T3.GroupTheory.Roots.DefectBasis`<br>`T3.GroupTheory.GeneratorRank`<br>`T3.ForMathlib.Subgroup` | proved | proof_checked |
| Remark 4.10<br>`structure.shared_triple_roots` | triple roots で生成元を共有する refinement | label なし<br>1177–1182 | `T3.GroupTheory.Roots.SharedTriple` | planned | unchecked |
| Proposition 4.11<br>`structure.ec_central_series` | e.c. 群の内部中心列一致と単一の交換子・三重交換子表示 | `proposition:structure of e.c. model`<br>1185–1195 | `T3.ModelTheory.ExistentiallyClosedGroups` | proved | proof_checked |
| Proposition 4.12<br>`structure.strict_envelope` | 総生成元数 15n²、内部中心列一致、LCS strict envelope | `proposition:bdd LCS`<br>1212–1220 | `T3.ModelTheory.StrictEnvelope` | proved | proof_checked |

## 宣言と項目内の進捗

### `preliminaries.exponent_three`

予定宣言: 型の設計時に決める。

実在宣言: [T3.HasExponentThree](../T3/GroupTheory/Basic.lean#L32), [T3.hasExponentThree_iff_exponent_dvd](../T3/GroupTheory/Basic.lean#L39), [T3.hasExponentThree_of_subsingleton](../T3/GroupTheory/Basic.lean#L48), [FirstOrder.Language.group](../T3/ModelTheory/GroupLanguage.lean#L51), [FirstOrder.Language.Theory.group](../T3/ModelTheory/GroupLanguage.lean#L190), [FirstOrder.Group.groupOfModelGroup](../T3/ModelTheory/GroupLanguage.lean#L242), [FirstOrder.Group.embeddingOfInjectiveMonoidHom](../T3/ModelTheory/GroupLanguage.lean#L304), [FirstOrder.Group.coe_substructure_closure_eq](../T3/ModelTheory/GroupLanguage.lean#L392), [T3.exponentGroupTheory](../T3/ModelTheory/ExponentThree.lean#L104), [T3.exponentThreeTheory](../T3/ModelTheory/ExponentThree.lean#L131), [T3.exponentThreeTheory_model_iff](../T3/ModelTheory/ExponentThree.lean#L139), [T3.exponentThreeTheory_isPiTwo](../T3/ModelTheory/ExponentThree.lean#L148), [T3.finite_substructure_closure_of_model_exponentThreeTheory](../T3/ModelTheory/ExponentThree.lean#L187), [T3.exponentThreeTheory_isLocallyFinite](../T3/ModelTheory/ExponentThree.lean#L204)。

実際の群言語とTₙ、n=3でHasExponentThreeとの同値、Π₂、局所有限性を証明。元の演算を保ち自明群・任意宇宙の群・空の生成集合を含む。companion/e.c.の最後の判定のみ既存canonical semantic universeを継承する。

### `preliminaries.notation`

予定宣言: 型の設計時に決める。

実在宣言: なし。

自由群・coproduct の cube quotient 表示と普遍性、および反復交換子を実装。残る記法の個別対応は未登録。

| part ID | 内容 / 原文行 | formalization | fidelity | 実在宣言 |
| --- | --- | --- | --- | --- |
| commutator | 交換子 aba⁻¹b⁻¹ / 147 | planned | unchecked | なし |
| iterated_commutator | 左結合の反復交換子 / 148 | proved | proof_checked | [T3.iteratedCommutator](../T3/GroupTheory/CentralSeries.lean#L161) |
| conjugation | 共役 aᵇ=b⁻¹ab / 149 | planned | unchecked | なし |
| variety | 指数 3 の variety V₃ / 150 | proved | proof_checked | [T3.exponentThreeTheory_model_iff](../T3/ModelTheory/ExponentThree.lean#L139) |
| free_product | 通常の自由積 / 151 | planned | unchecked | なし |
| normal_closure | 集合の normal closure / 152 | planned | unchecked | なし |
| generator_rank | 最小生成元数 d(G) / 155 | partial | unchecked | [Group.fg_of_generating_family](../T3/GroupTheory/GeneratorRank.lean#L43), [T3.AssociatedGraded.finrank_layerOne_le_rank](../T3/GroupTheory/GeneratorRank.lean#L195), [T3.AssociatedGraded.finrank_layerTwo_le_rank](../T3/GroupTheory/GeneratorRank.lean#L207) |
| coproduct | variety 内の coproduct と quotient 表示 / 156 | proved | proof_checked | [T3.Coproduct](../T3/GroupTheory/Coproduct/Basic.lean#L33), [T3.Coproduct.lift](../T3/GroupTheory/Coproduct/Basic.lean#L69), [T3.Coproduct.hom_ext](../T3/GroupTheory/Coproduct/Basic.lean#L86) |
| free_group | 自由指数群と Burnside 群 B(r,3) / 162 | proved | proof_checked | [T3.Free](../T3/GroupTheory/Free/Basic.lean#L122), [T3.Free.of](../T3/GroupTheory/Free/Basic.lean#L132), [T3.Free.lift](../T3/GroupTheory/Free/Basic.lean#L157), [T3.Free.hom_ext](../T3/GroupTheory/Free/Basic.lean#L170) |

### `model_theory.basic_definitions`

予定宣言: 型の設計時に決める。

実在宣言: なし。

項目1–6を実装。構文的model completenessとcanonical universeでの意味論的条件の同値、一般有限言語の図式、局所有限性の下で全QF図式のT同値類の有限代表集合まで証明。companion/e.c.のモデル量化はType (max u v)を用いる既存規約に従う。これらの他宇宙への移行bridgeは独立の残件であり、論文全体の完了を意味しない。

| part ID | 内容 / 原文行 | formalization | fidelity | 実在宣言 |
| --- | --- | --- | --- | --- |
| companion | 双方のモデルへの埋込み / 180 | proved | proof_checked | [FirstOrder.Language.Theory.ModelsEmbedInto](../T3/ModelTheory/ModelCompanion.lean#L49), [FirstOrder.Language.Theory.IsCompanion](../T3/ModelTheory/ModelCompanion.lean#L70) |
| model_complete | 全式を existential formula に書き換える model completeness / 181 | proved | proof_checked | [FirstOrder.Language.Theory.IsModelComplete](../T3/ModelTheory/ModelCompanion.lean#L104), [FirstOrder.Language.Theory.IsModelComplete.realize_embedding_iff](../T3/ModelTheory/ModelCompanion.lean#L136), [FirstOrder.Language.Theory.AllEmbeddingsElementary.exists_finset_qfDiagram_entails](../T3/ModelTheory/ModelCompleteness.lean#L294), [FirstOrder.Language.Theory.AllEmbeddingsElementary.isModelComplete](../T3/ModelTheory/ModelCompleteness.lean#L395), [FirstOrder.Language.Theory.isModelComplete_iff_allEmbeddingsElementary](../T3/ModelTheory/ModelCompleteness.lean#L457) |
| model_companion | model-complete companion / 182 | proved | proof_checked | [FirstOrder.Language.Theory.IsModelCompanionOf](../T3/ModelTheory/ModelCompanion.lean#L162), [FirstOrder.Language.Theory.HasModelCompanion](../T3/ModelTheory/ModelCompanion.lean#L188) |
| existentially_closed | QF 行列をもつ existential formula に関する閉性 / 183 | proved | proof_checked | [FirstOrder.Language.Theory.IsExistentiallyClosed](../T3/ModelTheory/ModelCompanion.lean#L197) |
| pi_two | ∀∃ 文による同値な公理化 / 184 | proved | proof_checked | [FirstOrder.Language.BoundedFormula.IsUniversalExistential](../T3/ModelTheory/Inductive.lean#L51), [FirstOrder.Language.Theory.IsPiTwo](../T3/ModelTheory/Inductive.lean#L109) |
| finite_diagram | 有限 tuple の QF 図式と有限言語・局所有限性の下での有限性 / 185 | proved | proof_checked | [FirstOrder.Language.tupleQfDiagram](../T3/ModelTheory/FiniteDiagram.lean#L229), [FirstOrder.Language.realize_finiteGeneratedDiagram_iff_tupleQfDiagram](../T3/ModelTheory/FiniteDiagram.lean#L321), [FirstOrder.Language.Theory.IsLocallyFinite.exists_finite_tupleQfDiagram](../T3/ModelTheory/LocallyFinite.lean#L68), [FirstOrder.Language.Theory.IsLocallyFinite.exists_finite_qf_representatives](../T3/ModelTheory/UniformLocalFiniteness.lean#L208), [FirstOrder.Language.Theory.IsLocallyFinite.exists_finite_tupleQfDiagram_representatives](../T3/ModelTheory/UniformLocalFiniteness.lean#L241) |

### `model_theory.companion_iff_ec`

予定宣言: 型の設計時に決める。

実在宣言: [FirstOrder.Language.Theory.IsModelCompanionOf.models_iff_isExistentiallyClosed](../T3/ModelTheory/Inductive.lean#L202), [FirstOrder.Language.DirectLimit.models_of_isPiTwo](../T3/ModelTheory/PiTwoDirectLimit.lean#L76), [FirstOrder.Language.Theory.exists_isExistentiallyClosed_embedding](../T3/ModelTheory/ExistentiallyClosedExtension.lean#L326), [FirstOrder.Language.DirectLimit.realize_boundedFormula_of](../T3/ModelTheory/ElementaryChain.lean#L107), [FirstOrder.Language.Theory.isModelComplete_of_isExistentiallyClosedInModels](../T3/ModelTheory/RobinsonTest.lean#L433), [FirstOrder.Language.Theory.isModelCompanionOf_of_isExistentiallyClosed_iff](../T3/ModelTheory/ModelCompanionCriterion.lean#L43), [FirstOrder.Language.Theory.isModelCompanionOf_iff_models_iff_isExistentiallyClosed](../T3/ModelTheory/ModelCompanionCriterion.lean#L65)。

一般Π₂理論について全同値を証明。旧e.c.拡大・Robinson test・elementary chainを再利用し、普遍理論に限定されていた極限のモデル性を一般Π₂に拡張。finite-language/local-finiteness/amalgamationの追加仮定なし。逆向きも実際の存在式生成による構文的model completenessまで到達する。既存canonical Type (max u v)規約下で完成。任意の上位宇宙でのcompanion/e.c.への移行は別残件。

### `model_theory.local_finiteness`

予定宣言: 型の設計時に決める。

実在宣言: [FirstOrder.Language.Theory.IsLocallyFinite](../T3/ModelTheory/LocallyFinite.lean#L44), [FirstOrder.Language.Theory.IsLocallyFinite.finite_closure_range](../T3/ModelTheory/LocallyFinite.lean#L55)。

任意の有限subsetが生成する実際のSubstructureの有限性として定義。有限言語や生成部分構造がTのmodelであることは仮定しない。companion/e.c.定義と同じcanonical semantic universeを用い、他宇宙へのbridgeは未実装。

### `model_theory.uniform_local_finiteness`

予定宣言: 型の設計時に決める。

実在宣言: [FirstOrder.Language.Theory.IsLocallyFinite.exists_finite_qfType_cover](../T3/ModelTheory/UniformLocalFiniteness.lean#L89), [FirstOrder.Language.Theory.exists_card_closure_le_of_isLocallyFinite](../T3/ModelTheory/UniformLocalFiniteness.lean#L182)。

一般の局所有限T・有限言語について、compactnessで有限個の生成tupleのQF型が全モデルのtupleを覆うことを証明し、その生成部分構造の位数の最大値から共通上界を得る。任意n・card≤nの全有限subset・空集合を含む。有限部分構造自身にTmodel条件は要求しない。モデル宇宙はIsLocallyFiniteのcanonical規約どおり。

### `model_theory.bounded_amalgamation_criterion`

予定宣言: 型の設計時に決める。

実在宣言: [FirstOrder.Language.Theory.hasModelCompanion_iff_boundedAmalgamationObstructions](../T3/ModelTheory/BoundedAmalgamationCriterion.lean#L196), [FirstOrder.Language.Theory.extensionTheory](../T3/ModelTheory/BoundedAmalgamationCriterion.lean#L88), [FirstOrder.Language.Theory.AmalgamableOver](../T3/ModelTheory/Amalgamation.lean#L85), [FirstOrder.Language.Theory.IsLocallyFinite.exists_finite_bad_marked_cover](../T3/ModelTheory/FiniteObstructions.lean#L193), [FirstOrder.Language.extensionAxiom](../T3/ModelTheory/ExtensionAxioms.lean#L64)。

一般有限言語・Π₂・局所有限Tについて両方向完成。存在式の一様witness数から必要方向、有界生成障害の有限marked代表と実際のextension sentencesから十分方向を証明。有限A/B/C自身にはT-model条件を置かず空の構造も許す。上界は有限包含A→Bを固定して選び全e.c.MとA→Mに共通、Cの総生成元数を数える。モデル量化は既存canonical semantic universe規約。

| part ID | 内容 / 原文行 | formalization | fidelity | 実在宣言 |
| --- | --- | --- | --- | --- |
| model_companion | model companion の存在 / 219 | proved | proof_checked | [FirstOrder.Language.Theory.hasModelCompanion_of_boundedAmalgamationObstructions](../T3/ModelTheory/BoundedAmalgamationCriterion.lean#L172) |
| bounded_obstruction | e.c. モデル内の総生成元数が有界な非 amalgamation 障害 / 220 | proved | proof_checked | [FirstOrder.Language.Theory.BoundedAmalgamationObstructions](../T3/ModelTheory/BoundedAmalgamation.lean#L101), [FirstOrder.Language.Theory.HasModelCompanion.boundedAmalgamationObstructions](../T3/ModelTheory/BoundedAmalgamation.lean#L183), [FirstOrder.Language.Theory.IsModelCompanionOf.exists_bounded_nonamalgamation_obstruction](../T3/ModelTheory/BoundedAmalgamation.lean#L118) |

### `linear_algebra.graded_lie`

予定宣言: 型の設計時に決める。

実在宣言: なし。

| part ID | 内容 / 原文行 | formalization | fidelity | 実在宣言 |
| --- | --- | --- | --- | --- |
| grading | bracket の次数整合性 / 272 | planned | unchecked | なし |
| bilinear | bracket の双加法性 / 273 | planned | unchecked | なし |
| alternating | 交代性 / 274 | planned | unchecked | なし |
| jacobi | Jacobi 恒等式 / 275 | planned | unchecked | なし |

### `linear_algebra.degree_one_generation`

予定宣言: 型の設計時に決める。

実在宣言: なし。

| part ID | 内容 / 原文行 | formalization | fidelity | 実在宣言 |
| --- | --- | --- | --- | --- |
| antisymmetry | bracket の反対称性 / 283 | planned | unchecked | なし |
| generation | 次数 1 からの生成と各次数の bracket による生成 / 284 | planned | unchecked | なし |

### `linear_algebra.truncated_exterior`

予定宣言: 型の設計時に決める。

実在宣言: [T3.TruncatedExterior](../T3/LinearAlgebra/TruncatedExterior.lean#L35), [T3.TruncatedExterior.instLieRing](../T3/LinearAlgebra/TruncatedExterior.lean#L133), [T3.TruncatedExterior.instLieAlgebra](../T3/LinearAlgebra/TruncatedExterior.lean#L160), [T3.TruncatedExterior.ofOne_lie_ofOne](../T3/LinearAlgebra/TruncatedExterior.lean#L214), [T3.TruncatedExterior.ofTwo_lie_ofOne](../T3/LinearAlgebra/TruncatedExterior.lean#L222), [T3.TruncatedExterior.ofOne_lie_ofTwo](../T3/LinearAlgebra/TruncatedExterior.lean#L230), [T3.TruncatedExterior.ofThree_lie](../T3/LinearAlgebra/TruncatedExterior.lean#L236), [T3.TruncatedExterior.lie_ofThree](../T3/LinearAlgebra/TruncatedExterior.lean#L241), [T3.TruncatedExterior.ofTwo_lie_ofTwo](../T3/LinearAlgebra/TruncatedExterior.lean#L246), [T3.TruncatedExterior.grade](../T3/LinearAlgebra/TruncatedExterior.lean#L289), [T3.TruncatedExterior.grade_eq_bot](../T3/LinearAlgebra/TruncatedExterior.lean#L326), [T3.TruncatedExterior.instGradedBracket](../T3/LinearAlgebra/TruncatedExterior.lean#L334), [T3.TruncatedExterior.instDecomposition](../T3/LinearAlgebra/TruncatedExterior.lean#L421), [T3.TruncatedExterior.instGradedLieAlgebra](../T3/LinearAlgebra/TruncatedExterior.lean#L429)。

任意の F₃ ベクトル空間 V の mathlib 外冪 Λ¹V × Λ²V × Λ³V を用いる。次数 (1,1),(2,1) は正、(1,2) は負の外積で、次数和 ≥ 4 の bracket は零。LieRing・LieAlgebra と明示的内部直和分解・GradedLieAlgebra を構成。ℕ grading の次数 0 および ≥ 4 は零で、原稿の正次数 grading と一致する。Jacobi は三重外積の巡回性と標数 3 から証明し、有限次元や基底の仮定はない。

### `linear_algebra.block_homogeneous`

予定宣言: 型の設計時に決める。

実在宣言: [T3.IsBlockHomogeneous](../T3/LinearAlgebra/BlockDecomposition.lean#L43), [T3.isBlockHomogeneous_iff_iSup_eq](../T3/LinearAlgebra/BlockDecomposition.lean#L51), [T3.blockIntersections_independent](../T3/LinearAlgebra/BlockDecomposition.lean#L82)。

mathlibのDirectSum.Decompositionとhomogeneous predicateを用い、原稿のW=⨁(W∩Bᵢ)との同値をiSup等式と独立性で証明。任意index、一般Ring上のmoduleで成立し、原稿のvector spaceを含む。

### `linear_algebra.block_quotient`

予定宣言: 型の設計時に決める。

実在宣言: [T3.BlockDecomposition.QuotientBlock](../T3/LinearAlgebra/BlockDecomposition.lean#L97), [T3.BlockDecomposition.quotientEquiv](../T3/LinearAlgebra/BlockDecomposition.lean#L177), [T3.BlockDecomposition.quotientEquiv_mk_apply](../T3/LinearAlgebra/BlockDecomposition.lean#L203), [T3.BlockDecomposition.quotientEquiv_symm_lof_mk](../T3/LinearAlgebra/BlockDecomposition.lean#L222)。

各componentをその交差部分空間で割る具体的写像の核=W・全射性から、原稿のcanonical LinearEquivを構成。代表元の各成分の像と単一成分に対する逆写像の公式も証明。有限index仮定はない。

### `preliminaries.set_commutator`

予定宣言: 型の設計時に決める。

実在宣言: [T3.commutatorOfSets](../T3/GroupTheory/Basic.lean#L59), [T3.commutator_mem_commutatorOfSets](../T3/GroupTheory/Basic.lean#L68)。

任意の集合 A,B を扱う。Fact 2.15 の集合積に関する包含の公開 API に接続する。

### `preliminaries.central_series`

予定宣言: 型の設計時に決める。

実在宣言: なし。

mathlib のlower index nは原稿γₙ₊₁、upper index nはZₙ。任意群・任意nの再帰式と反復交換子による定義を接続。

| part ID | 内容 / 原文行 | formalization | fidelity | 実在宣言 |
| --- | --- | --- | --- | --- |
| lower | 下部中心列 γ₁=G, γₙ₊₁=[γₙ,G] / 328 | proved | proof_checked | [T3.lowerCentralSeries_initial](../T3/GroupTheory/CentralSeries.lean#L208), [T3.lowerCentralSeries_step](../T3/GroupTheory/CentralSeries.lean#L217) |
| upper | 反復交換子による上部中心列 Zₙ / 332 | proved | proof_checked | [T3.mem_upperCentralSeries_iff_forall_fin](../T3/GroupTheory/CentralSeries.lean#L192) |

### `preliminaries.upper_central_recursive`

予定宣言: 型の設計時に決める。

実在宣言: [T3.mem_upperCentralSeries_iff_forall_iteratedCommutator](../T3/GroupTheory/CentralSeries.lean#L170), [T3.mem_upperCentralSeries_iff_forall_fin](../T3/GroupTheory/CentralSeries.lean#L192)。

### `preliminaries.central_series_properties`

予定宣言: 型の設計時に決める。

実在宣言: なし。

一般群のまま証明。次数評価はThree Subgroups Lemmaをquotientで用い、nilpotency classの仮定は原稿どおり保持。

| part ID | 内容 / 原文行 | formalization | fidelity | 実在宣言 |
| --- | --- | --- | --- | --- |
| commutator_degree | [γᵢ,γⱼ]≤γᵢ₊ⱼ と次数商の可換性 / 346 | proved | proof_checked | [Subgroup.commutator_lowerCentralSeries_le](../T3/GroupTheory/CentralSeries.lean#L65), [Subgroup.isMulCommutative_lowerCentralSeries_quotient](../T3/GroupTheory/CentralSeries.lean#L137) |
| upper_bound | class≤n の群の γᵢ≤Zₙ₊₁₋ᵢ / 347 | proved | proof_checked | [Subgroup.lowerCentralSeries_le_upperCentralSeries](../T3/GroupTheory/CentralSeries.lean#L103) |

### `preliminaries.elementary_identities`

予定宣言: 型の設計時に決める。

実在宣言: なし。

全 11 項目を検証済み。項目 3 の Z₂ 非可換例は自由群 F₂ で実証し、γ₂ の可換性と合わせた。

| part ID | 内容 / 原文行 | formalization | fidelity | 実在宣言 |
| --- | --- | --- | --- | --- |
| quadruple_commutator | 四重交換子の消滅、nilpotency class≤3 / 359 | proved | proof_checked | [T3.commutator_quadruple](../T3/GroupTheory/Identities.lean#L665), [T3.lowerCentralSeries_three_eq_bot](../T3/GroupTheory/Identities.lean#L621) |
| central_series_inclusions | γ₃≤Z と γ₂≤Z₂ / 360 | proved | proof_checked | [T3.lowerCentralSeries_two_le_center](../T3/GroupTheory/Identities.lean#L609), [T3.commutator_le_upperCentralSeries_two](../T3/GroupTheory/Identities.lean#L673) |
| derived_abelian | γ₂ の可換性と、一般には Z₂ が可換でないこと / 361 | proved | proof_checked | [T3.isMulCommutative_commutator](../T3/GroupTheory/Identities.lean#L657), [T3.Free.not_isMulCommutative_upperCentralSeries_two_fin_two](../T3/GroupTheory/Free/Examples.lean#L69) |
| triple_cyclic | 三重交換子の巡回対称性と 2-Engel 性 / 362 | proved | proof_checked | [T3.commutator_triple_cyclic](../T3/GroupTheory/Identities.lean#L504), [T3.commutator_self_right](../T3/GroupTheory/Identities.lean#L139) |
| commutator_inverse | 各引数の逆元と交換子の逆元 / 363 | proved | proof_checked | [T3.commutator_inv_left](../T3/GroupTheory/Identities.lean#L686), [T3.commutator_inv_right](../T3/GroupTheory/Identities.lean#L694) |
| normal_closure_abelian | 同じ元の共役同士の可換性と principal normal closure の可換性 / 364 | proved | proof_checked | [T3.commutator_conjugates](../T3/GroupTheory/Identities.lean#L703), [T3.isMulCommutative_normalClosure](../T3/GroupTheory/Identities.lean#L711) |
| triple_swap | 三重交換子の第 1・2 引数交換による反転 / 365 | proved | proof_checked | [T3.commutator_triple_swap](../T3/GroupTheory/Identities.lean#L492) |
| commutator_mul_right | 右引数の積に対する交換子展開 / 366 | proved | proof_checked | [T3.commutator_mul_right](../T3/GroupTheory/Identities.lean#L720) |
| commutator_mul_left | 左引数の積に対する交換子展開 / 367 | proved | proof_checked | [T3.commutator_mul_left](../T3/GroupTheory/Identities.lean#L730) |
| subgroup_product_right | 集合の右積に対する交換子部分群包含 / 368 | proved | proof_checked | [T3.commutatorOfSets_mul_right](../T3/GroupTheory/Identities.lean#L763) |
| subgroup_product_left | 集合の左積に対する交換子部分群包含 / 369 | proved | proof_checked | [T3.commutatorOfSets_mul_left](../T3/GroupTheory/Identities.lean#L797) |

### `preliminaries.free_coproduct`

予定宣言: 型の設計時に決める。

実在宣言: [T3.Free.sumEquivCoproduct](../T3/GroupTheory/Coproduct/Basic.lean#L221)。

非交和を Sum で符号化し、生成元に関して自然な同型を両方向の普遍性から構成。有限性・非空性の仮定なし。

### `preliminaries.coproduct_factor_injective`

予定宣言: 型の設計時に決める。

実在宣言: [T3.Coproduct.fst](../T3/GroupTheory/Coproduct/Basic.lean#L99), [T3.Coproduct.snd](../T3/GroupTheory/Coproduct/Basic.lean#L106), [T3.Coproduct.inl_injective](../T3/GroupTheory/Coproduct/Basic.lean#L172), [T3.Coproduct.inr_injective](../T3/GroupTheory/Coproduct/Basic.lean#L181)。

原稿の retraction による証明。各因子への retraction と単射性には、その因子の指数 3 条件だけで十分。有限性は仮定しない。

### `preliminaries.associated_graded`

予定宣言: 型の設計時に決める。

実在宣言: なし。

実際の中心列商上に交換子を二変数とも降下し、標準ZMod3双線形bracketを構成。DirectSum上のLieRing/LieAlgebra/GradedLieAlgebra、全正次数での代表元式と次数0の消滅を証明。

| part ID | 内容 / 原文行 | formalization | fidelity | 実在宣言 |
| --- | --- | --- | --- | --- |
| degree_piece | 次数 n の中心列商 / 394 | proved | proof_checked | [T3.AssociatedGraded.Layer](../T3/GroupTheory/AssociatedGraded.lean#L99), [T3.AssociatedGraded.layerModule](../T3/GroupTheory/AssociatedGraded.lean#L165), [T3.AssociatedGraded.GradedModule](../T3/GroupTheory/AssociatedGraded.lean#L557) |
| bracket | 代表元による bracket と graded Lie algebra 構造 / 395 | proved | proof_checked | [T3.AssociatedGraded.bracketLayer](../T3/GroupTheory/AssociatedGraded/Bracket.lean#L182), [T3.AssociatedGraded.bracketLayer_mk](../T3/GroupTheory/AssociatedGraded/Bracket.lean#L192), [T3.AssociatedGraded.gradedLieRing](../T3/GroupTheory/AssociatedGraded/Lie.lean#L106), [T3.AssociatedGraded.gradedLieAlgebra](../T3/GroupTheory/AssociatedGraded/Lie.lean#L121), [T3.AssociatedGraded.grade](../T3/GroupTheory/AssociatedGraded/Lie.lean#L203), [T3.AssociatedGraded.gradedLieGrading](../T3/GroupTheory/AssociatedGraded/Lie.lean#L220), [T3.AssociatedGraded.bracket_lof_mk](../T3/GroupTheory/AssociatedGraded/Lie.lean#L190), [T3.AssociatedGraded.grade_zero](../T3/GroupTheory/AssociatedGraded/Lie.lean#L238) |

### `preliminaries.associated_graded_properties`

予定宣言: 型の設計時に決める。

実在宣言: なし。

次数4以上の消滅、全Lie algebra上の三重bracket恒等式、次数1像によるLie生成を、任意指数3群について証明。

| part ID | 内容 / 原文行 | formalization | fidelity | 実在宣言 |
| --- | --- | --- | --- | --- |
| degree_four | gr₄=0 / 414 | proved | proof_checked | [T3.AssociatedGraded.layer_four_subsingleton](../T3/GroupTheory/AssociatedGraded.lean#L310) |
| triple_identities | 三重 bracket の巡回性と反復引数の消滅 / 415 | proved | proof_checked | [T3.AssociatedGraded.triple_bracket_cyclic](../T3/GroupTheory/AssociatedGraded/Lie.lean#L141), [T3.AssociatedGraded.triple_bracket_self](../T3/GroupTheory/AssociatedGraded/Lie.lean#L149) |
| generation | gr₁ による Lie algebra の生成 / 417 | proved | proof_checked | [T3.AssociatedGraded.lieSubalgebra_eq_top_of_degree_one](../T3/GroupTheory/AssociatedGraded/Generation.lean#L69), [T3.AssociatedGraded.lieSpan_range_lof_one_eq_top](../T3/GroupTheory/AssociatedGraded/Generation.lean#L95) |

### `preliminaries.graded_image`

予定宣言: 型の設計時に決める。

実在宣言: なし。

ambient のK∩γₙによるfiltrationを用いる。原稿の商とのcanonical LinearEquivと代表元の式を証明。intrinsicな中心列への取り違えなし。

| part ID | 内容 / 原文行 | formalization | fidelity | 実在宣言 |
| --- | --- | --- | --- | --- |
| initial_form | 元の次数 i の像 / 424 | proved | proof_checked | [T3.AssociatedGraded.mk](../T3/GroupTheory/AssociatedGraded.lean#L106), [T3.AssociatedGraded.mk_eq_zero](../T3/GroupTheory/AssociatedGraded.lean#L123) |
| subgroup_image | 部分群 K の graded image と中心列商の同型 / 426 | proved | proof_checked | [T3.AssociatedGraded.subgroupImage](../T3/GroupTheory/AssociatedGraded.lean#L461), [T3.AssociatedGraded.mem_subgroupImage](../T3/GroupTheory/AssociatedGraded.lean#L469), [T3.AssociatedGraded.subgroupLayerEquiv](../T3/GroupTheory/AssociatedGraded.lean#L483), [T3.AssociatedGraded.subgroupLayerEquiv_mk](../T3/GroupTheory/AssociatedGraded.lean#L500) |

### `preliminaries.associated_graded_examples`

予定宣言: 型の設計時に決める。

実在宣言: なし。

項目2を完了。全次数で中心列の直積公式と、射影・包含から得るcanonicalなlayerのLinearEquivを証明。項目1の可換群と項目3のF₂の具体的記述は未完了。

| part ID | 内容 / 原文行 | formalization | fidelity | 実在宣言 |
| --- | --- | --- | --- | --- |
| abelian | 可換群の graded / 441 | planned | unchecked | なし |
| product | 直積の中心列と graded 直和 / 442 | proved | proof_checked | [T3.AssociatedGraded.term_prod](../T3/GroupTheory/AssociatedGraded/Product.lean#L45), [T3.AssociatedGraded.layerProdEquiv](../T3/GroupTheory/AssociatedGraded/Product.lean#L84), [T3.AssociatedGraded.layerProdEquiv_apply](../T3/GroupTheory/AssociatedGraded/Product.lean#L93) |
| free_two | F₂ の中心列と gr₁・gr₂ / 443 | planned | unchecked | なし |

### `preliminaries.associated_graded_map`

予定宣言: 型の設計時に決める。

実在宣言: [T3.AssociatedGraded.mapLayer](../T3/GroupTheory/AssociatedGraded.lean#L510), [T3.AssociatedGraded.mapLayer_mk](../T3/GroupTheory/AssociatedGraded.lean#L519), [T3.AssociatedGraded.mapLie](../T3/GroupTheory/AssociatedGraded/Lie.lean#L275), [T3.AssociatedGraded.map_bracket](../T3/GroupTheory/AssociatedGraded/Lie.lean#L263), [T3.AssociatedGraded.mapLie_mem_grade](../T3/GroupTheory/AssociatedGraded/Lie.lean#L291), [T3.AssociatedGraded.mapLie_id](../T3/GroupTheory/AssociatedGraded/Lie.lean#L302), [T3.AssociatedGraded.mapLie_comp](../T3/GroupTheory/AssociatedGraded/Lie.lean#L313)。

各次数商の誘導線形写像を実際のLieHomに持ち上げ、bracket・grading・恒等写像・合成の保存を証明。

### `preliminaries.lcs_strictness`

予定宣言: 型の設計時に決める。

実在宣言: なし。

| part ID | 内容 / 原文行 | formalization | fidelity | 実在宣言 |
| --- | --- | --- | --- | --- |
| derived | γ₂ の交わり条件 / 465 | proved | proof_checked | [T3.IsStrict](../T3/GroupTheory/CentralSeries.lean#L228), [T3.isStrict_iff_comap_subtype](../T3/GroupTheory/CentralSeries.lean#L334) |
| third | γ₃ の交わり条件 / 466 | proved | proof_checked | [T3.IsStrict](../T3/GroupTheory/CentralSeries.lean#L228), [T3.isStrict_iff_comap_subtype](../T3/GroupTheory/CentralSeries.lean#L334) |

### `preliminaries.graded_injectivity_strictness`

予定宣言: 型の設計時に決める。

実在宣言: なし。

原稿の仮定のまま、実際のassociated graded LieHomについて両主張を証明。全次数の線形写像の検出結果を同じ写像のLieHom構造へ接続する。

| part ID | 内容 / 原文行 | formalization | fidelity | 実在宣言 |
| --- | --- | --- | --- | --- |
| injective | gr(f) の単射性から f の単射性 / 473 | proved | proof_checked | [T3.AssociatedGraded.injective_of_mapLie_injective](../T3/GroupTheory/AssociatedGraded/Lie.lean#L324) |
| strict_iff | 単射 f に対する gr(f) の単射性と strictness の同値 / 474 | proved | proof_checked | [T3.AssociatedGraded.mapLie_injective_iff_isStrict](../T3/GroupTheory/AssociatedGraded/Lie.lean#L332) |

### `preliminaries.central_series_coincide`

予定宣言: 型の設計時に決める。

実在宣言: [T3.CentralSeriesCoincide](../T3/GroupTheory/CentralSeries.lean#L238), [T3.centralSeriesCoincide_iff](../T3/GroupTheory/CentralSeries.lean#L349)。

### `preliminaries.strict_of_internal`

予定宣言: 型の設計時に決める。

実在宣言: なし。

| part ID | 内容 / 原文行 | formalization | fidelity | 実在宣言 |
| --- | --- | --- | --- | --- |
| inclusions | 部分群の下部中心列から上部中心列への包含鎖 / 513 | proved | proof_checked | [T3.centralSeries_inclusions](../T3/GroupTheory/CentralSeries.lean#L299) |
| strict | 内部中心列一致から strictness / 514 | proved | proof_checked | [T3.isStrict_of_centralSeriesCoincide](../T3/GroupTheory/CentralSeries.lean#L316) |

### `preliminaries.finite_normal_form`

予定宣言: 型の設計時に決める。

実在宣言: [T3.freeOrderExponent](../T3/GroupTheory/Free/NormalForm.lean#L67), [T3.Free.finite](../T3/GroupTheory/Free/Collection.lean#L1082), [T3.Free.natCard_eq_pow_freeOrderExponent](../T3/GroupTheory/Free/NormalForm.lean#L599), [T3.Free.normalWord](../T3/GroupTheory/Free/NormalForm.lean#L756), [T3.Free.existsUnique_normalWord](../T3/GroupTheory/Free/NormalForm.lean#L882)。

任意の有限線形順序付き生成集合について正確な位数と原稿の三ブロック積の存在一意性を証明。生成元の積は昇順。座標群全体を自由群と同一視しない。

### `preliminaries.infinite_normal_form`

予定宣言: 型の設計時に決める。

実在宣言: [T3.Free.exists_finset_map](../T3/GroupTheory/Free/FiniteSupport.lean#L51), [T3.Free.collect_toLvdW_injective](../T3/GroupTheory/Free/FiniteSupport.lean#L175), [T3.Free.normalWordFinsupp](../T3/GroupTheory/Free/InfiniteNormalForm.lean#L104), [T3.Free.existsUnique_normalWordFinsupp](../T3/GroupTheory/Free/InfiniteNormalForm.lean#L279)。

任意の線形順序付き生成集合について、有限支持の三係数族による実際の昇順積の存在一意性。有限・可算・非空の仮定なし。有限版と有限生成支持への還元を再利用。

### `preliminaries.free_graded_equiv`

予定宣言: 型の設計時に決める。

実在宣言: [T3.Free.exteriorLinearEquiv](../T3/GroupTheory/Free/ExteriorLie.lean#L41), [T3.Free.exteriorLinearEquiv_map_bracket](../T3/GroupTheory/Free/ExteriorLie.lean#L146), [T3.Free.exteriorLieEquiv](../T3/GroupTheory/Free/ExteriorLie.lean#L163), [T3.Free.exteriorLieEquiv_grade](../T3/GroupTheory/Free/ExteriorLie.lean#L191)。

実際の中心列商から、任意の基底付きF₃ベクトル空間VのΛ¹V・Λ²V・Λ³Vへのσ₁・σ₂・σ₃を構成。原稿の生成元上の式、双線形性によるbracket保存、各次数部分空間の像の等式を証明し、σの直和をgraded LieEquivとして完成。昇順の対・三つ組の外冪基底を用いる原稿の証明経路を保つ。

| part ID | 内容 / 原文行 | formalization | fidelity | 実在宣言 |
| --- | --- | --- | --- | --- |
| degree_one | 次数 1 の同型 / 556 | proved | proof_checked | [T3.Free.sigmaOne](../T3/GroupTheory/Free/Exterior.lean#L106), [T3.Free.sigmaOne_of](../T3/GroupTheory/Free/Exterior.lean#L163) |
| degree_two | 次数 2 の同型 / 557 | proved | proof_checked | [T3.Free.sigmaTwo](../T3/GroupTheory/Free/Exterior.lean#L115), [T3.Free.sigmaTwo_commutator](../T3/GroupTheory/Free/Exterior.lean#L173), [T3.Free.sigmaTwo_bracketLayer](../T3/GroupTheory/Free/ExteriorBracket.lean#L127) |
| degree_three | 次数 3 の同型と Lie 構造の整合 / 559 | proved | proof_checked | [T3.Free.sigmaThree](../T3/GroupTheory/Free/Exterior.lean#L125), [T3.Free.sigmaThree_tripleCommutator](../T3/GroupTheory/Free/Exterior.lean#L185), [T3.Free.sigmaThree_bracketLayer](../T3/GroupTheory/Free/ExteriorBracket.lean#L197) |

### `preliminaries.infinite_free_graded`

予定宣言: 型の設計時に決める。

実在宣言: [T3.Free.sigmaOne](../T3/GroupTheory/Free/Exterior.lean#L106), [T3.Free.sigmaTwo](../T3/GroupTheory/Free/Exterior.lean#L115), [T3.Free.sigmaThree](../T3/GroupTheory/Free/Exterior.lean#L125), [T3.Free.exteriorLieEquiv](../T3/GroupTheory/Free/ExteriorLie.lean#L163), [T3.Free.exteriorLieEquiv_grade](../T3/GroupTheory/Free/ExteriorLie.lean#L191)。

Prop 2.29の同じσとgraded LieEquivが任意の線形順序付き生成集合Iと基底bに対して成立する。有限・可算・非空の仮定はない。有限積化するのは非零になり得る3次数だけであり、rankを有限に制限しない。

### `preliminaries.graded_quotient`

予定宣言: 型の設計時に決める。

実在宣言: [T3.AssociatedGraded.mapLayer_quotient_surjective](../T3/GroupTheory/GradedQuotient.lean#L137), [T3.AssociatedGraded.mapLayer_quotient_ker](../T3/GroupTheory/GradedQuotient.lean#L145), [T3.AssociatedGraded.quotientLayerEquiv](../T3/GroupTheory/GradedQuotient.lean#L179), [T3.AssociatedGraded.quotientLayerEquiv_mapLayer](../T3/GroupTheory/GradedQuotient.lean#L190), [T3.AssociatedGraded.quotientLayerEquiv_mk](../T3/GroupTheory/GradedQuotient.lean#L200)。

任意の正規部分群Nと全次数nについて、自然な商写像の全射性と核=grₙ(N)を証明して原稿の同型を得る。代表元上の公式も含む。有限生成・strictnessは仮定しない。

### `main.conjugate_width`

予定宣言: 型の設計時に決める。

実在宣言: [T3.principalNormalForm](../T3/GroupTheory/ConjugateWidth.lean#L81), [T3.principalNormalForm_eq_normalClosure](../T3/GroupTheory/ConjugateWidth.lean#L118), [T3.exists_conjList_of_mem_normalClosure](../T3/GroupTheory/ConjugateWidth.lean#L150), [T3.normalClosure_eq_conjList](../T3/GroupTheory/ConjugateWidth.lean#L197)。

原稿のEₐ={aᵏ[a,g]}の部分群性とnormal closureとの一致を経て、全ての元を高々3個のg⁻¹*a*gの積として表す。逆元a⁻¹を別の共役因子として許してはいない。k=0,1,2に応じた原稿の圧縮を使い、自明なaと任意rankを含む。

### `main.bounded_support`

予定宣言: 型の設計時に決める。

実在宣言: [T3.Support.normalClosureIn](../T3/GroupTheory/Support.lean#L36), [T3.Support.exists_finite_support](../T3/GroupTheory/Support.lean#L97), [T3.Support.exists_bounded_support](../T3/GroupTheory/Support.lean#L171), [T3.Support.exists_bounded_support_set](../T3/GroupTheory/Support.lean#L197), [T3.Support.exists_bounded_support_rank](../T3/GroupTheory/Support.lean#L216)。

全Lemma3.2完成。生成列のみでclass2 collectionを行い、H/γ₃からliftしてm+1個のG元で右共役を圧縮する。各principal幅3と有限relator族の積分解・支持和集合から3(m+1)n。C=closureY≤G、literal Group.rank Cの上界、実際のH₀内部normal closureのcertificateを同時に得る。Set Δはencard≤nから有限性を導く。B.FGは自然数rankの定義域のみ、ambient有限性や非自明性を追加しない。

| part ID | 内容 / 原文行 | formalization | fidelity | 実在宣言 |
| --- | --- | --- | --- | --- |
| bound | d(C)≤3(m+1)n / 673 | proved | proof_checked | [T3.Support.exists_bounded_support_rank](../T3/GroupTheory/Support.lean#L216) |
| certificate | H₀=〈C,B,Δ〉内で normal-closure certificate が成立 / 674 | proved | proof_checked | [T3.Support.exists_bounded_support_set](../T3/GroupTheory/Support.lean#L197) |

### `main.proposition_a`

予定宣言: 型の設計時に決める。

実在宣言: [T3.exists_bounded_strict_envelope](../T3/ModelTheory/StrictEnvelope.lean#L169), [T3.strictEnvelopeBound](../T3/ModelTheory/StrictEnvelope.lean#L43)。

Proposition 4.12 から全モデル・部分群に一様な関数の存在を明示的に証明。f₀(n)=15n²、n=0も含む。e.c. の量化は既存のcanonical semantic universeであり、一般モデル宇宙へのbridgeは別途未完成。

### `main.bounded_witness`

予定宣言: 型の設計時に決める。

実在宣言: [T3.Amalgamation.relator](../T3/GroupTheory/Amalgamation.lean#L42), [T3.Amalgamation.relations](../T3/GroupTheory/Amalgamation.lean#L49), [T3.Amalgamation.Pushout](../T3/GroupTheory/Amalgamation.lean#L63), [T3.Amalgamation.AmalgamableOver](../T3/GroupTheory/Amalgamation.lean#L190), [T3.Amalgamation.amalgamableOver_iff](../T3/GroupTheory/Amalgamation.lean#L201), [T3.Amalgamation.amalgamableOver_of_amalgam](../T3/GroupTheory/Amalgamation.lean#L216), [T3.Amalgamation.normalClosure_relators_eq_of_closure_range_eq_top](../T3/GroupTheory/Amalgamation.lean#L266), [T3.Amalgamation.exists_witness_of_generating_family](../T3/GroupTheory/Amalgamation.lean#L289), [T3.witnessBound](../T3/Main/BoundedWitness.lean#L35), [T3.exists_bounded_nonamalgamation_witness](../T3/Main/BoundedWitness.lean#L112), [T3.exists_uniform_nonamalgamation_bound](../T3/Main/BoundedWitness.lean#L173), [T3.rank_eq_finrank_layerOne](../T3/GroupTheory/GeneratorRank/Cardinality.lean#L51), [T3.rank_le_log_three_natCard](../T3/GroupTheory/GeneratorRank/Cardinality.lean#L113), [T3.rank_le_freeOrderExponent_of_injective](../T3/GroupTheory/GeneratorRank/Cardinality.lean#L144), [T3.Coproduct.exists_bounded_factor_support](../T3/GroupTheory/Coproduct/Support.lean#L38), [T3.Support.normalClosureIn_mono_ambient](../T3/GroupTheory/Support/Transport.lean#L33), [T3.Support.mem_normalClosure_of_mem_normalClosureIn](../T3/GroupTheory/Support/Transport.lean#L50)。

f(m)=15((3m+4)t(m)+1)²を明示。rank A≤log₃|A|≤log₃|B|≤t(m)、3(m+1)nのsupport、Aと左の証人の付加、strict envelope、Φの単射性と関係族の逆像等式による内部normal closureの移送を原稿順に証明。左右両証人・零rank・自明群を含む。Mのe.c.はcanonical semantic Type、Bは任意宇宙。一般モデル宇宙へのbridgeは別途残る。

| part ID | 内容 / 原文行 | formalization | fidelity | 実在宣言 |
| --- | --- | --- | --- | --- |
| obstruction | D と B が A 上で amalgamate しない / 709 | proved | proof_checked | [T3.exists_bounded_nonamalgamation_witness](../T3/Main/BoundedWitness.lean#L112) |
| bound | 総生成元数 d(D)≤f(m) / 710 | proved | proof_checked | [T3.exists_bounded_nonamalgamation_witness](../T3/Main/BoundedWitness.lean#L112) |

### `main.model_companion`

予定宣言: 型の設計時に決める。

実在宣言: [T3.exponentThreeTheory_hasModelCompanion_iff](../T3/ModelTheory/ExponentThree.lean#L213), [T3.exponentThreeTheory_hasModelCompanion_of_boundedAmalgamationObstructions](../T3/ModelTheory/ExponentThree.lean#L224), [T3.exponentThreeTheory_boundedAmalgamationObstructions](../T3/Main/ModelCompanion.lean#L48), [T3.has_model_companion](../T3/Main/ModelCompanion.lean#L122), [T3.GroupAmalgamation.amalgamableOver_embeddings_swap_iff](../T3/ModelTheory/GroupAmalgamation.lean#L117)。

Theorem3.3から一般のbounded obstructionを供給し、有限言語・Π₂・局所有限性によるFact2.6を適用。追加のbound仮定を残さずHasModelCompanionを証明。有限構造のgroup/modelはT₃の普遍性から回復し、元のbaseと全生成数を保つ。結論は既存canonical semantic universe、一般モデル宇宙へのbridgeは未完成。

### `structure.basis_lift`

予定宣言: 型の設計時に決める。

実在宣言: [T3.Free.presentation_of_basis](../T3/GroupTheory/Presentation.lean#L184), [T3.Free.liftLayerOneEquiv](../T3/GroupTheory/Presentation.lean#L150), [T3.Free.liftLayerOneEquiv_apply](../T3/GroupTheory/Presentation.lean#L159), [T3.commutator_le_sup_commutator_of_sup_eq_top](../T3/GroupTheory/Generation.lean#L81), [T3.commutator_right_le_of_sup_commutator_eq_top](../T3/GroupTheory/Generation.lean#L119)。

任意の指定済みBasis I F₃ (Layer G 1)と代表元aを引数にし、そのFree.liftが全射で核がderivedに入ることを証明。原稿のG=Hγ₂から二段階の交換子包含を経る群の生成性を保つ。Iに有限・可算・順序の仮定はなく、次数1の同型の証明中でのみ順序を選択する。

### `structure.normal_closure_graded`

予定宣言: 型の設計時に決める。

実在宣言: [T3.AssociatedGraded.subgroupImage_normalClosure_one](../T3/GroupTheory/GradedNormalClosure.lean#L322)。

一般Gと任意K≤derivedについて全3項を証明。実際の積K[K,G]を経て、次数3では先にL∩γ₃=(K∩γ₃)[K,G]を計算する。Kの非斉次relationを成分ごとに分離しない。bracket部分空間はmathlib Submodule.map₂で表し、有限性・自由性・Kの正規性を追加しない。

| part ID | 内容 / 原文行 | formalization | fidelity | 実在宣言 |
| --- | --- | --- | --- | --- |
| normal_closure | L=K[K,G] / 807 | proved | proof_checked | [T3.normalClosure_eq_sup_commutator](../T3/GroupTheory/GradedNormalClosure.lean#L63), [T3.mem_normalClosure_iff_mul_commutator](../T3/GroupTheory/GradedNormalClosure.lean#L107), [T3.normalClosure_le_commutator](../T3/GroupTheory/GradedNormalClosure.lean#L120) |
| degree_two | normal closure の次数 2 の像 / 808 | proved | proof_checked | [T3.AssociatedGraded.subgroupImage_normalClosure_two](../T3/GroupTheory/GradedNormalClosure.lean#L269) |
| degree_three | normal closure の次数 3 の像 / 809 | proved | proof_checked | [T3.AssociatedGraded.normalClosure_inf_term_three](../T3/GroupTheory/GradedNormalClosure.lean#L282), [T3.AssociatedGraded.subgroupImage_commutator_top](../T3/GroupTheory/GradedNormalClosure.lean#L224), [T3.AssociatedGraded.subgroupImage_normalClosure_three](../T3/GroupTheory/GradedNormalClosure.lean#L306) |

### `structure.graded_coproduct`

予定宣言: 型の設計時に決める。

実在宣言: [T3.Coproduct.Presentation.quotientEquiv](../T3/GroupTheory/Coproduct/Presentation.lean#L362), [T3.Coproduct.Presentation.presentationMap_ker](../T3/GroupTheory/Coproduct/Presentation.lean#L407), [T3.Coproduct.Presentation.relationSubgroup_inf_term](../T3/GroupTheory/Coproduct/Presentation.lean#L506), [T3.Coproduct.Presentation.subgroupImage_relationKernel_two](../T3/GroupTheory/Coproduct/Relations.lean#L268), [T3.Coproduct.Presentation.subgroupImage_relationKernel_three](../T3/GroupTheory/Coproduct/Relations.lean#L283), [T3.AssociatedGraded.bracketLayer_subgroupImage_top_le](../T3/GroupTheory/Coproduct/Relations.lean#L40), [T3.AssociatedGraded.subgroupImage_map_of_leftInverse](../T3/GroupTheory/AssociatedGraded/Subgroup.lean#L84), [T3.Free.sigmaThree_mapLayer](../T3/GroupTheory/Free/ExteriorNaturality.lean#L82), [T3.Free.sigmaThree_bracket_factors_one_two](../T3/GroupTheory/Free/ExteriorNaturality.lean#L216), [T3.ExteriorTensor.tensorEquiv](../T3/LinearAlgebra/ExteriorTensor.lean#L228), [T3.ExteriorTensor.tensorEquiv_symm_comp_lof](../T3/LinearAlgebra/ExteriorTensor.lean#L263), [T3.ExteriorTensor.blockTensorEquiv](../T3/LinearAlgebra/ExteriorTensor.lean#L382), [T3.Coproduct.Presentation.subgroupImage_relationKernel_three_eq_four_blocks](../T3/GroupTheory/Coproduct/Relations.lean#L329), [T3.Coproduct.freeSumLayerTwoMap_bijective](../T3/GroupTheory/Coproduct/FreeGraded.lean#L332), [T3.Coproduct.freeSumLayerThreeMap_bijective](../T3/GroupTheory/Coproduct/FreeGraded.lean#L359), [T3.Coproduct.layerThreeBlockMap_ker_map_freeSum](../T3/GroupTheory/Coproduct/QuotientMaps.lean#L180), [T3.Coproduct.freeSumLayerThreeMap_quotient_square](../T3/GroupTheory/Coproduct/QuotientMaps.lean#L230), [T3.AssociatedGraded.mapLayer_ker](../T3/GroupTheory/GradedQuotient.lean#L103)。

全項目完成。自由表示・関係像の四成分分解・符号付き外積tensor同型・kernel輸送によりcanonical η₂/η₃の全単射性を証明。η₁–η₃は基底非依存の元の写像と自然性を保ち任意群/任意rankを許す。実際のgraded Lie algebraの全次数blockでbracket包含も証明。η₁だけは原稿のpresentation経由を短縮し同じ写像をcoproduct普遍性とretractionで直接証明する。

| part ID | 内容 / 原文行 | formalization | fidelity | 実在宣言 |
| --- | --- | --- | --- | --- |
| isomorphisms | η₁,η₂,η₃ の次数別同型 / 846 | proved | proof_checked | [T3.Coproduct.layerOneEquiv](../T3/GroupTheory/Coproduct/Graded.lean#L152), [T3.Coproduct.layerTwoMap](../T3/GroupTheory/Coproduct/Graded.lean#L217), [T3.Coproduct.layerThreeMap](../T3/GroupTheory/Coproduct/Graded.lean#L233), [T3.Coproduct.mixedMap_tmul](../T3/GroupTheory/Coproduct/Graded.lean#L200), [T3.Coproduct.layerOneEquiv_natural](../T3/GroupTheory/Coproduct/Graded.lean#L292), [T3.Coproduct.layerTwoMap_natural](../T3/GroupTheory/Coproduct/Graded.lean#L327), [T3.Coproduct.layerThreeMap_natural](../T3/GroupTheory/Coproduct/Graded.lean#L340), [T3.Coproduct.layerTwoEquiv](../T3/GroupTheory/Coproduct/GradedEquiv.lean#L101), [T3.Coproduct.layerThreeEquiv](../T3/GroupTheory/Coproduct/GradedEquiv.lean#L110), [T3.Coproduct.layerTwoEquiv_apply](../T3/GroupTheory/Coproduct/GradedEquiv.lean#L120), [T3.Coproduct.layerThreeEquiv_apply](../T3/GroupTheory/Coproduct/GradedEquiv.lean#L129) |
| bracket | 直和・tensor block 上の bracket / 858 | proved | proof_checked | [T3.Coproduct.block](../T3/GroupTheory/Coproduct/BlockBracket.lean#L66), [T3.Coproduct.bracket_block_le](../T3/GroupTheory/Coproduct/BlockBracket.lean#L270), [T3.Coproduct.bracket_mem_block](../T3/GroupTheory/Coproduct/BlockBracket.lean#L342), [T3.Coproduct.bracket_mixedMap_tmul_inl](../T3/GroupTheory/Coproduct/BlockBracket.lean#L208), [T3.Coproduct.bracket_mixedMap_tmul_inr](../T3/GroupTheory/Coproduct/BlockBracket.lean#L222) |

### `structure.strict_coproduct`

予定宣言: 型の設計時に決める。

実在宣言: [T3.Coproduct.map_injective_of_strict](../T3/GroupTheory/Coproduct/Strict.lean#L114), [T3.Coproduct.mapLayer_map_injective](../T3/GroupTheory/Coproduct/Strict.lean#L62)。

任意の指数3群とstrict inclusionについて、η₁–η₃の自然性と体上のtensor単射性から全graded層の単射性を得てProposition2.24で群の単射性を導く。有限性仮定なし。

### `structure.free_two_stabilization`

予定宣言: 型の設計時に決める。

実在宣言: [T3.Coproduct.freeTwo_stabilization](../T3/GroupTheory/Coproduct/CentralSeries.lean#L44), [T3.Coproduct.FreeTwoSeparation.exists_triple_bracket_ne_zero](../T3/GroupTheory/Coproduct/FreeTwoSeparation.lean#L86), [T3.Coproduct.FreeTwoSeparation.exists_bracket_ne_zero](../T3/GroupTheory/Coproduct/FreeTwoSeparation.lean#L127), [T3.AssociatedGraded.centralSeriesCoincide_of_bracket_separation](../T3/GroupTheory/Coproduct/CentralSeriesCriterion.lean#L119)。

原稿の任意の非自明GとF₂についてfull statementを証明。ClaimAは第一層の左右成分、ClaimBはα₂/α₁/α₁′/β₂の分岐を保ちη₃逆座標で非零を検出。群交換子へ戻し中心列の等式を得る。旧有限群+F₃ theoremとは区別する。

### `structure.simultaneous_commutator_roots`

予定宣言: 型の設計時に決める。

実在宣言: [T3.CommutatorRoots.Ambient](../T3/GroupTheory/Roots/Commutator.lean#L74), [T3.CommutatorRoots.relator](../T3/GroupTheory/Roots/Commutator.lean#L81), [T3.CommutatorRoots.kernel](../T3/GroupTheory/Roots/Commutator.lean#L97), [T3.CommutatorRoots.Extension](../T3/GroupTheory/Roots/Commutator.lean#L158), [T3.CommutatorRoots.baseMap](../T3/GroupTheory/Roots/Commutator.lean#L165), [T3.CommutatorRoots.kernel_eq_sup_commutator](../T3/GroupTheory/Roots/Commutator.lean#L139), [T3.CommutatorRoots.mem_normalClosure_singleton_iff](../T3/GroupTheory/Roots/Commutator.lean#L340), [T3.CommutatorRoots.mem_kernel_iff_mul_commutator](../T3/GroupTheory/Roots/Commutator.lean#L368), [T3.CommutatorRoots.coefficients_eq_zero](../T3/GroupTheory/Roots/Commutator.lean#L246), [T3.CommutatorRoots.centralWord_eq_one](../T3/GroupTheory/Roots/Commutator.lean#L443), [T3.CommutatorRoots.baseMap_injective](../T3/GroupTheory/Roots/Commutator.lean#L505), [T3.CommutatorRoots.baseMap_root](../T3/GroupTheory/Roots/Commutator.lean#L188)。

原稿のG*F₂ₙを全relatorで一括して割る具体的商と自然なbase embeddingの単射性を完成。ClaimAはK[K,H₀]とsingletonのF₃係数表示、ClaimBは独立な自由第二層のpair係数、ClaimCはη₃逆のmixed(1,2)成分からsᵢ=0→pure左成分0→a=1。任意G/任意rank/n=0/gᵢ=1を含む。

### `structure.derived_strictification`

予定宣言: 型の設計時に決める。

実在宣言: [T3.AssociatedGraded.finite_layerOne_of_generating_family](../T3/GroupTheory/GeneratorRank.lean#L130), [T3.AssociatedGraded.finrank_layerOne_le_of_generating_family](../T3/GroupTheory/GeneratorRank.lean#L151), [T3.AssociatedGraded.finrank_layerOne_le_rank](../T3/GroupTheory/GeneratorRank.lean#L195), [T3.AssociatedGraded.exists_layer_kernel_basis_representatives](../T3/GroupTheory/Roots/DefectBasis.lean#L46), [T3.AssociatedGraded.exists_derived_defect_generators](../T3/GroupTheory/Roots/DefectBasis.lean#L114), [T3.DerivedStrictification.Extension](../T3/GroupTheory/Roots/DerivedStrictification.lean#L47), [T3.DerivedStrictification.baseMap](../T3/GroupTheory/Roots/DerivedStrictification.lean#L54), [T3.DerivedStrictification.enlarged](../T3/GroupTheory/Roots/DerivedStrictification.lean#L70), [T3.DerivedStrictification.newGenerators_card_le](../T3/GroupTheory/Roots/DerivedStrictification.lean#L108), [T3.DerivedStrictification.enlarged_eq_closure](../T3/GroupTheory/Roots/DerivedStrictification.lean#L117), [T3.DerivedStrictification.comap_commutator_quotientMap](../T3/GroupTheory/Roots/DerivedStrictification.lean#L143), [T3.DerivedStrictification.inf_commutator_eq](../T3/GroupTheory/Roots/DerivedStrictification.lean#L186), [T3.DerivedStrictification.rank_enlarged_le](../T3/GroupTheory/Roots/DerivedStrictification.lean#L276), [T3.DerivedStrictification.exists_derived_strictification](../T3/GroupTheory/Roots/DerivedStrictification.lean#L306), [Subgroup.exists_mul_mul_commutator_of_mem_sup](../T3/ForMathlib/Subgroup.lean#L39)。

実際の一次graded kernelの基底を群へ持ち上げ、defectの生成等式と個数≤rank Cを証明。同時交換子商でDをCの像と2d個の自由生成元から生成する。商は一次商を保ち、coproductの二つの射影で成分を分離してD∩γ₂(H)=γ₂(D)を得る。追加≤2m、総rank≤3m、同一宇宙の単射拡大。有限性・非自明性のambient仮定なし。

| part ID | 内容 / 原文行 | formalization | fidelity | 実在宣言 |
| --- | --- | --- | --- | --- |
| bound | C に追加する生成元数≤2m / 1079 | proved | proof_checked | [T3.DerivedStrictification.newGenerators_card_le](../T3/GroupTheory/Roots/DerivedStrictification.lean#L108), [T3.DerivedStrictification.rank_enlarged_le](../T3/GroupTheory/Roots/DerivedStrictification.lean#L276), [T3.DerivedStrictification.exists_derived_strictification](../T3/GroupTheory/Roots/DerivedStrictification.lean#L306) |
| strict | D∩γ₂(H)=γ₂(D) / 1080 | proved | proof_checked | [T3.DerivedStrictification.inf_commutator_eq](../T3/GroupTheory/Roots/DerivedStrictification.lean#L186), [T3.DerivedStrictification.derived_strict](../T3/GroupTheory/Roots/DerivedStrictification.lean#L248), [T3.DerivedStrictification.exists_derived_strictification](../T3/GroupTheory/Roots/DerivedStrictification.lean#L306) |

### `structure.simultaneous_triple_roots`

予定宣言: 型の設計時に決める。

実在宣言: [T3.TripleRoots.relator](../T3/GroupTheory/Roots/Triple.lean#L73), [T3.TripleRoots.kernel](../T3/GroupTheory/Roots/Triple.lean#L80), [T3.TripleRoots.Extension](../T3/GroupTheory/Roots/Triple.lean#L225), [T3.TripleRoots.baseMap](../T3/GroupTheory/Roots/Triple.lean#L232), [T3.TripleRoots.baseMap_injective](../T3/GroupTheory/Roots/Triple.lean#L269), [T3.TripleRoots.baseMap_root](../T3/GroupTheory/Roots/Triple.lean#L277)。

原稿どおりG×Free(Fin(3*n))を全関係式((gᵢ)⁻¹,[xᵢ,yᵢ,zᵢ])のnormal closureで一括して割る。中心性からclosureに落とし、独立な三重座標で有限積の整数係数をmod3で回収してGとの交叉が自明と証明。任意G、空族、重複する中心元、自明な中心元を含み、逐次の単一root構成には置き換えない。

### `structure.lcs_strictification`

予定宣言: 型の設計時に決める。

実在宣言: [T3.AssociatedGraded.finite_layerTwo_of_generating_family](../T3/GroupTheory/GeneratorRank.lean#L141), [T3.AssociatedGraded.finrank_layerTwo_le_of_generating_family](../T3/GroupTheory/GeneratorRank.lean#L163), [T3.AssociatedGraded.finrank_layerTwo_le_rank](../T3/GroupTheory/GeneratorRank.lean#L207), [T3.AssociatedGraded.exists_layer_kernel_basis_representatives](../T3/GroupTheory/Roots/DefectBasis.lean#L46), [T3.AssociatedGraded.exists_lowerCentral_defect_generators](../T3/GroupTheory/Roots/DefectBasis.lean#L135), [T3.LowerCentralStrictification.enlargedSubgroup](../T3/GroupTheory/Roots/LowerCentralStrictification.lean#L54), [T3.LowerCentralStrictification.enlargedSubgroup_eq_sup](../T3/GroupTheory/Roots/LowerCentralStrictification.lean#L84), [T3.LowerCentralStrictification.kernel_le_lowerCentralSeries](../T3/GroupTheory/Roots/LowerCentralStrictification.lean#L112), [T3.LowerCentralStrictification.kernel_le_product_derived](../T3/GroupTheory/Roots/LowerCentralStrictification.lean#L128), [T3.LowerCentralStrictification.isStrict_enlargedSubgroup](../T3/GroupTheory/Roots/LowerCentralStrictification.lean#L184), [T3.LowerCentralStrictification.exists_generating_finset](../T3/GroupTheory/Roots/LowerCentralStrictification.lean#L236), [T3.LowerCentralStrictification.rank_enlargedSubgroup_le](../T3/GroupTheory/Roots/LowerCentralStrictification.lean#L267), [T3.LowerCentralStrictification.exists_strict_extension](../T3/GroupTheory/Roots/LowerCentralStrictification.lean#L300), [Subgroup.map_inf_of_ker_le](../T3/ForMathlib/Subgroup.lean#L76)。

第一strict性を使って二次graded kernelを原稿の欠損商と同定し、その基底代表元を≤binom(rank C,2)個選ぶ。G×Free(Fin(3d))の同時商とC×Freeの像Dを構成し、kernel包含・直積中心列・商内の交叉から両strict等式を証明。追加≤3*binom(m,2)、総rank≤m+3*binom(m,2)、Dの有限生成性と同一宇宙の単射拡大を返す。自明群と空の欠損族を含む。

| part ID | 内容 / 原文行 | formalization | fidelity | 実在宣言 |
| --- | --- | --- | --- | --- |
| bound | C に追加する生成元数≤3·binom(n,2) / 1138 | proved | proof_checked | [T3.LowerCentralStrictification.exists_generating_finset](../T3/GroupTheory/Roots/LowerCentralStrictification.lean#L236), [T3.LowerCentralStrictification.rank_enlargedSubgroup_le](../T3/GroupTheory/Roots/LowerCentralStrictification.lean#L267), [T3.LowerCentralStrictification.exists_strict_extension](../T3/GroupTheory/Roots/LowerCentralStrictification.lean#L300) |
| strict | D が γ₂ と γ₃ で strict / 1139 | proved | proof_checked | [T3.LowerCentralStrictification.isStrict_enlargedSubgroup](../T3/GroupTheory/Roots/LowerCentralStrictification.lean#L184), [T3.LowerCentralStrictification.exists_strict_extension](../T3/GroupTheory/Roots/LowerCentralStrictification.lean#L300) |

### `structure.shared_triple_roots`

予定宣言: 型の設計時に決める。

実在宣言: なし。

主定理では使わない refinement だが、論文全体の対応対象に含める。

### `structure.ec_central_series`

予定宣言: 型の設計時に決める。

実在宣言: [T3.ExistentiallyClosedGroups.exists_group_embedding](../T3/ModelTheory/ExistentiallyClosedGroups.lean#L48), [T3.ExistentiallyClosedGroups.exists_copy_of_tuples](../T3/ModelTheory/ExistentiallyClosedGroups.lean#L67), [T3.ExistentiallyClosedGroups.nontrivial](../T3/ModelTheory/ExistentiallyClosedGroups.lean#L87)。

既存canonical semantic universe内のe.c.T₃モデルについて3結論完成。有限生成部分群を局所有限性で有限化し、有限図式embeddingにより全パラメータを固定して等式・不等式を転送。具体的同時root商のn=1特殊化から単一交換子/三重交換子、非自明性をe.c.から導いてF₂の分離から中心列一致を得る。Nontrivial/有限性を仮定しない。

| part ID | 内容 / 原文行 | formalization | fidelity | 実在宣言 |
| --- | --- | --- | --- | --- |
| central_series | 上下中心列の逆順での一致 / 1186 | proved | proof_checked | [T3.ExistentiallyClosedGroups.centralSeriesCoincide](../T3/ModelTheory/ExistentiallyClosedGroups.lean#L279) |
| commutator_width | γ₂ の各元が単一の交換子 / 1190 | proved | proof_checked | [T3.ExistentiallyClosedGroups.commutator_eq_setOf_commutator](../T3/ModelTheory/ExistentiallyClosedGroups.lean#L323) |
| triple_width | γ₃ の各元が単一の三重交換子 / 1193 | proved | proof_checked | [T3.ExistentiallyClosedGroups.lowerCentralSeries_two_eq_setOf_triple_commutator](../T3/ModelTheory/ExistentiallyClosedGroups.lean#L308) |

### `structure.strict_envelope`

予定宣言: 型の設計時に決める。

実在宣言: [T3.strictEnvelopeBound](../T3/ModelTheory/StrictEnvelope.lean#L43), [T3.three_stage_rank_le_strictEnvelopeBound](../T3/ModelTheory/StrictEnvelope.lean#L50), [T3.StrictEnvelope.exists_centralSeries_extension](../T3/ModelTheory/StrictEnvelope.lean#L68), [T3.exists_strict_envelope](../T3/ModelTheory/StrictEnvelope.lean#L129)。

二段階の同時strictification、D₂∐F₂、内部中心列一致、C全体を固定する有限図式転送を原稿順に証明。有限生成性と有限性の同値を使用し、C=1/n=0を別分岐で処理。代数的構成は任意宇宙、e.c.の結論はcanonical semantic universe。一般モデル宇宙へのbridgeは未完成。

| part ID | 内容 / 原文行 | formalization | fidelity | 実在宣言 |
| --- | --- | --- | --- | --- |
| bound | d(D)≤15n² / 1217 | proved | proof_checked | [T3.exists_strict_envelope](../T3/ModelTheory/StrictEnvelope.lean#L129) |
| internal | D 自身の上下中心列が逆順に一致し、D≤LCS M / 1218 | proved | proof_checked | [T3.exists_strict_envelope](../T3/ModelTheory/StrictEnvelope.lean#L129) |
