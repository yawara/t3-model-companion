# Lean 形式化の構成案

2026-09-09 に雛形の実装を開始し、2026-09-10 に補助補題の配置方針を更新した。
以下は全体の配置方針であり、未実装のパス・宣言名も含む。
現在の実装状況は [論文対応表](../docs/paper-map.md) を参照する。
対象は `T3_modelcompanion_v4.tex`、SHA256
`79745dfa1660a827c51ec3c6b2006ee9d6243cb4702f97a75e5b55357b89f50b`。

**数学的な内容で実装を分け、論文の掲載順で読める Lean の入口と対応表を設ける。**
個々の公開宣言にも原稿の所在を残す。論文の番号・節順と、Lean の名前・import 順を
独立に保つことで、原稿の改訂と証明の分割の両方に対応する。

## 1. ライブラリと入口

ライブラリ名・import の接頭辞は短い `T3` を推奨する。対象の版番号は名前に含めない。

```text
T3.lean                         全数学モジュールの import 集約
T3/
  Paper.lean                    論文順の案内。公開結果を import し、docstring で対応を示す
  GroupTheory/                  汎用の部分群補題、指数 3 の群論、自由群、graded、roots
    Subgroup.lean
    Free/
    Coproduct/
    Roots/
  LinearAlgebra/                汎用の線形代数補題、graded Lie、truncated exterior、block quotient
    DirectSum.lean
    LinearMapQuotient.lean
    TensorProduct.lean
  ModelTheory/                  一般モデル理論と指数 3 への接続
  Main/                         有界障害の主定理と model companion の系
Tests/                          公理依存・公開 API 等の検査
scripts/                        lint、対応表の整合性検査
docs/
  paper-map.toml                論文項目と公開宣言の対応の正本
  paper-map.md                  上記から生成する論文順の閲覧用一覧
```

`Paper.lean` は論文を読みながら開く入口、各数学モジュールは証明を読む入口とする。
`Paper.lean` に番号付き alias theorem を大量に作る必要はない。
`T3.lean` と `Paper.lean` は末端の集約で、数学モジュールから import しない。
検査プログラムは数学ライブラリの集約に含めない。

共有する汎用補題は、その数学的対象に対応する `GroupTheory`、`LinearAlgebra`、
`ModelTheory` 等に置く。用途が一つの構成に限られる準備は、その構成のモジュールに置く。
upstream 候補かどうかを配置軸にした `ForMathlib` 層は設けない。
論文との対応は module docstring、各宣言の `Paper-ID`、論文対応表に保持する。
汎用の主張であることと、論文のどの証明を支えるかは別々に記録する。

補助補題の具体的な配置は次のとおり。

| 数学的内容 | モジュール | 宣言の namespace |
| --- | --- | --- |
| 外部直和の標準的な各成分への分解 | `T3/LinearAlgebra/DirectSum.lean` | `DirectSum` |
| 部分群の join の分解、核を含む部分群との交わりの像 | `T3/GroupTheory/Subgroup.lean` | `Subgroup` |
| 核の対応による線形写像の商への同型降下 | `T3/LinearAlgebra/LinearMapQuotient.lean` | `LinearMap` |
| 非零純テンソル、テンソル積写像の核 | `T3/LinearAlgebra/TensorProduct.lean` | `TensorProduct` |
| 直和上の固定濃度部分集合の分解 | `T3/LinearAlgebra/ExteriorTensor.lean` の準備部分 | `Set.powersetCard` |

共有する低層補題は、その使用先の構成を import しない。
特定の構成の準備部分に置いた汎用補題も、既存 namespace の宣言名を保つ。

## 2. モジュールと論文項目の対応

下表は**公開結果の置き場**であり、最初からすべての証明用ファイルを作る指示ではない。
原則として、一つの大きな構成、または密接に関連した数個の補題を一モジュールとする。
長い正規形・compactness・coproduct 計算は、実装時に数学的な中間結果でさらに分ける。

`GT`、`LA`、`MT` はそれぞれ `T3/GroupTheory`、`T3/LinearAlgebra`、
`T3/ModelTheory`。各パスには `.lean` を補う。
番号は現在の TeX の共有 theorem counter から得た表示情報であり、固定 ID ではない。

| 現 v4 の項目 | TeX label または内容 | 公開モジュール案 |
| --- | --- | --- |
| §2 冒頭、Notation 2.1 | 指数の規約、交換子、共役、生成元数 | `GT/Basic` |
| Definition 2.2 | companion、model completeness、e.c.、Π₂、有限図式 | `MT/ModelCompanion`、`MT/ModelCompleteness`、`MT/Inductive`、`MT/FiniteDiagram`、`MT/UniformLocalFiniteness` |
| Fact 2.3 | Π₂ 理論の companion と e.c. class | `MT/Inductive`、`MT/ModelCompanionCriterion` |
| Definition 2.4、Fact 2.5 | 局所有限性と一様有限性 | `MT/LocallyFinite`、`MT/UniformLocalFiniteness` |
| Fact 2.6 | `fact:locally finiteness and model companion` | `MT/BoundedAmalgamationCriterion`、`MT/BoundedAmalgamation`、`MT/FiniteObstructions`、`MT/ExtensionAxioms` |
| Definition 2.7、Remark 2.8 | graded Lie と degree 1 による生成 | `LA/GradedLie` |
| Example 2.9 | `example:Grassmann algebra` | `LA/TruncatedExterior` |
| Definition 2.10、Proposition 2.11 | block-homogeneous subspace と quotient | `LA/BlockDecomposition` |
| Definition 2.12、Remark 2.13、Fact 2.14 | 上下中心列と一般的性質 | `GT/CentralSeries` |
| Fact 2.15 | `fact:elementary equations` | `GT/Identities` |
| Fact 2.16 | 自由生成集合の直和と coproduct | `GT/Coproduct/Basic` |
| Lemma 2.17 | coproduct の因子の単射性 | `GT/Coproduct/Basic` |
| Definition 2.18、Lemma 2.19、Notation 2.20 | associated graded、初期成分、部分群の graded image | `GT/AssociatedGraded`、`GT/AssociatedGraded/Bracket`、`GT/AssociatedGraded/Lie`、`GT/AssociatedGraded/Generation` |
| Example 2.21 | 可換群、直積、自由群 F₂ の graded | `GT/AssociatedGradedExamples`、`GT/AssociatedGraded/Product` |
| Definition 2.22 | 誘導写像 gr(f) | `GT/AssociatedGraded`、`GT/AssociatedGraded/Lie` |
| Definition 2.23 | LCS strictness | `GT/CentralSeries` |
| Proposition 2.24 | `proposition:gr(f) and LCS` | `GT/AssociatedGraded`、`GT/AssociatedGraded/Lie` |
| Definition 2.25、Lemma 2.26 | 内部中心列一致、それから任意 ambient 内の strictness | `GT/CentralSeries` |
| Fact 2.27 | `fact:Levi and van der Waerden` | `GT/Free/NormalForm` |
| Remark 2.28 | `remark:infinite dim` | `GT/Free/FiniteSupport`、`GT/Free/InfiniteNormalForm` |
| Proposition 2.29 | `proposition:gr(F) is Grassmann algebra` | `GT/Free/Graded`、`GT/Free/Exterior`、`GT/Free/ExteriorBracket`、`GT/Free/ExteriorLie` |
| Remark 2.30 | 無限 rank の graded 同型 | `GT/Free/ExteriorLie` |
| Lemma 2.31 | `lemma:gr of quotient` | `GT/GradedQuotient` |
| Proposition 3.1 | `proposition:bounded number of conjugates` | `GT/ConjugateWidth` |
| Lemma 3.2 | `lemma:witness in bdd support` | `GT/Support` |
| Proposition A | TeX 697–700、Proposition 4.12 から得る | `MT/StrictEnvelope` |
| Theorem 3.3 | `thm:main` | `T3/Main/BoundedWitness` |
| Corollary 3.4 | T₃ の model companion の存在 | `T3/Main/ModelCompanion` |
| Proposition 4.1 | `proposition:lift` | `GT/Generation`、`GT/Presentation` |
| Lemma 4.2 | `lemma:gr of normal closure` | `GT/GradedNormalClosure` |
| Proposition 4.3 | `proposition:gr of free product` | `GT/Coproduct/GradedEquiv`、`GT/Coproduct/Graded`、`GT/Coproduct/BlockBracket`、`GT/Coproduct/FreeGraded`、`GT/Coproduct/QuotientMaps`、`GT/Coproduct/Presentation`、`GT/Coproduct/Relations`、`LA/ExteriorLowDegree` |
| Lemma 4.4 | `lemma:free-product-amalgam` | `GT/Coproduct/Strict` |
| Lemma 4.5 | `lemma:coincidence of central series` | `GT/Coproduct/CentralSeries` |
| Lemma 4.6 | `lemma:basic commutator root` | `GT/Roots/Commutator` |
| Lemma 4.7 | `lemma:commutator root` | `GT/Roots/DerivedStrictification` |
| Lemma 4.8 | `lemma:triple commutator root` | `GT/Roots/Triple` |
| Lemma 4.9 | `lemma:number of generators for triple commutator roots` | `GT/Roots/LowerCentralStrictification` |
| Remark 4.10 | triple roots の生成元共有 | `GT/Roots/SharedTriple` |
| Proposition 4.11 | `proposition:structure of e.c. model` | `MT/ExistentiallyClosedGroups` |
| Proposition 4.12 | `proposition:bdd LCS` | `MT/StrictEnvelope` |

これで現原稿の番号付き 47 項目と Proposition A の所在を網羅する。
一つの Fact の複数項目は `parts` で区別し、必要なら複数の公開宣言を対応させる。
特に Fact 2.15 の恒等式群を一つの巨大な連言定理にまとめる必要はない。
Remarks、Examples に数学的主張がある場合も記録し、主定理で使わないものはその旨を示す。
§1、§5、§6 の現時点の執筆用 placeholder は Lean 定理の未証明とは数えない。

さらに、本文に独立した番号はないが必要となる公開補助境界を設ける。

| モジュール案 | 役割 |
| --- | --- |
| `GT/Free/Basic` | 自由指数 3 群と普遍性 |
| `GT/Free/FiniteSupport` | 有限生成集合への還元、任意 rank の座標の単射性と有限支持 |
| `GT/Free/InfiniteNormalForm` | 有限支持係数族による実際の正規形の存在一意性 |
| `GT/AssociatedGraded/Truncation` | 実際の直和と非零になり得る3次数の積との同型 |
| `GT/GeneratorRank` | 既存 `Group.rank` と有限生成族による第一・第二層の有限次元性・上界 |
| `GT/Amalgamation` | 群の amalgam、関係式による pushout、因子の kernel による障害 |
| `MT/FiniteDiagram` | 有限構造の図式、実現と embedding の対応 |
| `MT/ExponentThree` | T₃ と代数的指数条件の対応、Π₂ 性、局所有限性 |
| `MT/GroupLanguage` | 群の embedding/amalgam と一階構造の embedding/amalgam の対応 |

`ExponentThree` には自由群の有限性を使って局所有限性を証明する部分がある。
群論の `Basic` からこのモジュールを逆に import しない。

数値関数も論文との対応を優先し、対応する結果のモジュールで定義する。

| 論文の関数 | Lean の定義名案 | 定義するモジュール | 論文上の所在 |
| --- | --- | --- | --- |
| `t(n) = n + n.choose 2 + n.choose 3` | `T3.freeOrderExponent` | `GT/Free/NormalForm` | Fact 2.27：自由群の位数 `3 ^ t(n)` |
| `f₀(n) = 15 * n ^ 2` | `T3.strictEnvelopeBound` | `MT/StrictEnvelope` | Proposition 4.12：Proposition A の上界を供給 |
| `f(m) = f₀((3*m+4)*t(m)+1)` | `T3.witnessBound` | `T3/Main/BoundedWitness` | Theorem 3.3 の証明 |

各関数に付随する算術補題も同じモジュールに置く。関数を使う後続モジュールは、
その定義元を import する。関数の namespace は `T3` のままとし、配置と宣言名を分ける。

## 3. namespace と命名

ファイルパスは import の整理、namespace は数学的対象の整理に使う。
`T3.GroupTheory.Coproduct.Strict` のようにディレクトリ階層全体を宣言名へ写さない。

| 対象 | namespace 案 |
| --- | --- |
| 指数 3 固有の述語、主要定理、数値関数 | `T3` |
| 自由指数 3 群、coproduct の操作と補題 | `T3.Free`、`T3.Coproduct` |
| associated graded の操作と補題 | `T3.AssociatedGraded` |
| truncated exterior Lie algebra | `T3.TruncatedExterior` |
| 一般の companion、e.c.、局所有限理論 | `FirstOrder.Language.Theory` |
| 既存の群・線形代数 API の汎用補題 | `Subgroup`、`MonoidHom`、`LinearMap` 等、その対象の既存 namespace |

`T3` 固有の仮定を扱う結果を、無関係な汎用 namespace に無理に追加しない。
`Section4`、`Lemma44`、`V4` は namespace や数学的な宣言名には使わない。

ファイル名は UpperCamelCase、定理名は原則 snake_case、データ・写像は lowerCamelCase、
型・述語は UpperCamelCase とする。既存名を定理名に埋め込む場合なども含め、
[mathlib の命名規約](https://leanprover-community.github.io/contribute/naming.html)に合わせる。
例えば次のような公開名を想定する。型の設計時に既存 API との整合を確認する。

```text
T3.IsStrict                                      述語
T3.CentralSeriesCoincide                          述語
T3.strictEnvelopeBound                            ℕ → ℕ の関数
T3.AssociatedGraded.freeLieEquiv                   Lie 同型というデータ
T3.Coproduct.map_injective_of_strict               Lemma 4.4
T3.exists_strict_envelope                         Proposition 4.12 の完全な結論
T3.exists_bounded_nonamalgamation_witness          Theorem 3.3
T3.has_model_companion                            Corollary 3.4
```

Proposition A は、4.12 の結果から明示的な `strictEnvelopeBound` を取り出す通常の系とする。
同じ主張の番号違いだけを理由とする alias は不要で、対応表から既存の宣言を指してよい。
公開 API に不要な計算補題は `private` または小さな対象 namespace に収める。

## 4. Lean から論文へ戻るための記載

各数学モジュールの module docstring に、対象項目・主要宣言・証明経路を短く記す。
各論文対応宣言の docstring にも、安定 ID、原文 label、現行の表示番号を付ける。
次は**docstring の書式例**であり、未証明 theorem を作るためのコードではない。

```lean
/-- The comparison map on coproducts induced by a strict inclusion is injective.

Paper-ID: structure.strict_coproduct
TeX: T3_modelcompanion_v4.tex, `lemma:free-product-amalgam` (v4 Lemma 4.4).
The proof uses the natural block isomorphisms of Proposition 4.3.
-/
```

主キーには `structure.strict_coproduct` のような意味に基づく固定 ID を使う。
既存 TeX label は空白を含め原文のまま保持する。label がない項目も固定 ID を作り、
原稿の hash、行、短い主張で同定する。後から label が付いても ID は維持できる。
TeX 本文への label 追加は、Lean 側の追跡を始めるための前提にはしない。

`docs/paper-map.toml` は ID ごとの source locator、モジュール、宣言、対応状況を持つ。
一項目から複数宣言、一宣言から複数項目への対応を許す。
予定名 `planned_declarations` と実在する宣言 `declarations` を分ける。
表示番号と行は移動し得るため、ID の代わりには使わない。

未実装段階では前者だけを登録できる。状況は少なくとも次の二軸で分ける。

- Lean の状態：`planned` / `stated` / `proved`。
- 原稿との照合：`unchecked` / `statement_checked` / `proof_checked`。

`stated` は必要な定義と命題の型を記述できた状態で、証明済みを意味しない。
`proved` は実在する宣言の kernel 検証、公理依存、必要な lint を確認した状態。
`proof_checked` は主張・定数・量化範囲・主要構成を原稿と照合し、
標準的省略の展開や同値な符号化の bridge も記録した状態とする。
この二軸とは別に、どの source hash とコード revision を検査したかを残す。

対応表の検査は ID/label の存在、宣言の存在、所在、登録漏れを検出する。
ラベルの付いた theorem が論文に faithful であることまで自動認証するものではない。
初期段階で専用 Lean attribute や elaborator を作る必要はない。

## 5. 依存関係で守る境界

```text
群の基礎・恒等式 ─→ 中心列・strictness ─→ associated graded・quotient
自由群・正規形 + exterior Lie ─────────→ free graded 同型
両者 + presentation + normal closure ──→ coproduct の η₁–η₃・自然性
                                      ├→ strict coproduct
                                      ├→ 非自明 G と F₂ の中心列一致
                                      └→ 同時 roots → 次元評価による strictification
上記 + 有限図式・e.c. 転送 ────────────→ 15n² envelope → Proposition A
共役幅 → support + pushout + strict coproduct + Proposition A → Main theorem
一般の bounded-amalgamation criterion + Main theorem ───────→ 存在の系
```

これは主要な依存の概略であり、全 import の一覧ではない。
論文の §3 が §4 の結果を使う順序は、Lean では §4 に対応する実装から §3 へ流れる。

中心列の内部一致から strictness を導く Lemma 2.26 は純粋な群論として先に証明する。
`CentralSeries` が e.c. の結果を import する循環を作らない。
`Coproduct/Basic` は普遍性・因子 retraction までを扱い、graded 計算を逆輸入しない。
`Coproduct/Graded` は η₁–η₃ の自然性まで公開し、後続に基底の選択を漏らさない。
数値関数の依存も `Free/NormalForm` → `ModelTheory/StrictEnvelope` →
`Main/BoundedWitness` という数学的な流れに合わせる。`witnessBound` は最後のモジュールで
先行する二つの関数から定義し、正規形や envelope のモジュールから主定理を逆に import しない。

## 6. 初期に固定する数学的 API

- 指数 3 は `∀ g, g ^ 3 = 1`、すなわち `Monoid.exponent G ∣ 3`。
  自明群も含む条件を採用する。mathlib の指数 API へ接続する。
- `d(G)` は mathlib の `Group.rank` を使う。現 pin では `[Group.FG G]` が必要なので、
  構成段階では有限生成集合を明示し、有限生成性を得てから rank の不等式を公開する。
  総生成元数と追加生成元数は別の結論として記述する。
- 中心列は mathlib の定義を再利用し、論文の γ₁ に対する添字のずれを一箇所で文書化する。
  wrapper を使う場合も元の名前を shadow せず、対応補題を持たせる。
- `LieRing`、`LieAlgebra (ZMod 3)`、`GradedLieAlgebra`、`LinearEquiv`、`LieEquiv`、
  `TensorProduct`、外冪を使う。現在の mathlib の graded Lie API は内部直和を対象とする。
  群の LCS からの構成は新規に補い、単なる次数別 `MulEquiv` で完了とはしない。
  外部直和を内部 grading に接続する際も論文の次数を保ち、degree 0 は零とする。
- truncated exterior の Lie bracket は論文の符号付き定義を実装する。
  通常の外積代数の積から取った交換子 bracket とは異なるので、その Lie 構造を流用しない。
- coproduct は任意の群・任意 rank を扱う。η₃ の `(1,2)` block の符号、tensor の生成元上の
  値、自然性を明示する。無限 rank の座標には有限支持を使う。
- roots は `Fin n` 等で有限族を受け、論文の `G * F₂ₙ` または `G × F₃ₙ` の具体的 quotient、
  自然写像、単射性、root equations を公開する。
- `StrictEnvelope` の結論には `15n²` と D 自身の中心列一致を残す。
  support は `3(m+1)n`、主定理は `f(m) = 15 * ((3*m+4)*t(m)+1)^2` を得る。
- 一般の amalgamation は共通部分上で二つの embedding が一致する条件。
  像の交わりがちょうど共通部分になる strong amalgamation は要求しない。
  一般 criterion の有限部分構造自体を T のモデルとは仮定しない。
- 一般モデル理論の公開結果では Π₂・有限言語・局所有限性を原稿どおり扱い、
  存在から有界障害への必要方向も証明する。有限言語は全記号の集合が有限という条件。

これらは [fidelity 監査](paper-faithfulness-audit.md) で見つかった差分を、
公開する型とモジュールの境界で防ぐための設計である。

## 7. 初期実装の範囲と検査

`lakefile.toml`、toolchain、基礎の数学モジュール、`Paper.lean`、対応表と検査から実装する。
上表の全項目は `planned` として登録でき、未着手の空ファイルを一度に量産する必要はない。
依存する定義が整った段階で対象の型を固定し、証明を入れる。
命題を表す `def ... : Prop` を置くことと、その命題の証明は区別する。
未証明の本文を `sorry` や独自 `axiom` で埋めたものを公開ライブラリの雛形にはしない。

初期 pin は、監査済みの既存実装と合わせて Lean/mathlib v4.32.2、mathlib commit
`905b95818eb32af7874a58b427f50c1711a5e96c` を採用した。現時点の最新版を意味しない。
旧 repo の必要な補題を移す際は出典・著作権表示を保持し、独立した project として検証する。
隣接ディレクトリへの path dependency や、その終端への alias を形式化の完成とはしない。

検査方針は次を基本とする。

1. `autoImplicit = false`、`weak.linter.mathlibStandardSet = true`。
   mathlib 標準の header、行長、ファイル長を守り、例外なしを初期状態とする。
2. `lake build` と environment lint、全 project 数学ファイルの text/module-name lint。
   終了コード 0 に加え警告 0 を成功条件とする。
   最上位ファイルの直接 import だけを検査して全体の lint と呼ばない。
3. 全 project 数学宣言の公理依存を機械的に確認し、不許可の依存があれば検査を失敗させる。
   許容は `propext`、`Classical.choice`、`Quot.sound`。
   論文対応表に未登録の補助宣言も含め、終端だけの検査に限定しない。
4. source locator、対応宣言、import 集約、未証明項目の表示の整合性を確認する。

検査の実行入口は `python3 scripts/check.py`。入力のハッシュと各検査の結果は `.audit/` に残す。
初期実装の検証と、原稿全体の形式化の完成は別の状態として扱う。
下流 project 向けの標準集合と mathlib 本体専用の CI は区別する。
公式の [style guide](https://leanprover-community.github.io/contribute/style.html) と、
実際に pin した `Mathlib/Init.lean`、text linter の実装を基準にする。
