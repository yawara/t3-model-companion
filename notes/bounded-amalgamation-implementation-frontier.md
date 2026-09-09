# Fact 2.6 の実装 frontier

2026-09-10。コードは変更していない。本稿は実装済み定理と次に作る API を区別した設計記録。
Paper-ID: `model_theory.bounded_amalgamation_criterion`。
原稿は [T3_modelcompanion_v4.tex:214](/home/ywr/t3-model-companion/T3_modelcompanion_v4.tex:214)、
label `fact:locally finiteness and model companion`、statement 214–228、proof 230–263。
source SHA256: `79745dfa1660a827c51ec3c6b2006ee9d6243cb4702f97a75e5b55357b89f50b`。

**次のまとまった終端は一般の必要方向 `MC ⇒ bounded obstruction`。**
そのために新たな compactness 証明は不要であり、有限相対図式、存在式の一様な有限 witness、
amalgam の合成を接続すればよい。十分方向は既存の指数3用 extension scheme を一般化し、
禁止拡大の有限代表族を供給するのが主な未実装部分。

旧コード調査の [paper-faithfulness-audit.md:115](/home/ywr/t3-model-companion/notes/paper-faithfulness-audit.md:115)
は、一般 Π₂ criterion と必要方向が旧 repository に存在しないことを記録している。
[paper-mathematical-audit.md:202](/home/ywr/t3-model-companion/notes/paper-mathematical-audit.md:202)
には原稿の数学的確認がある。本 note はその説明を繰り返さず、現在の API からの接続を記す。
旧監査当時に未実装だった Fact 2.3 は現在完成している。

## 1. 終端の型と量化順

以下の新名称は**予定 API**。コードとして elaboration を検査したものではない。
`L : Language.{u,v}`、モデルの宇宙は既存規約の `Type (max u v)` とする。
`A,B,C` は構造であり、`T.ModelType` ではない。

```lean
-- FirstOrder.Language.Theory
def Embeddable (T : L.Theory) (C : Type (max u v)) [L.Structure C] : Prop :=
  ∃ N : T.ModelType.{u, v, max u v}, Nonempty (C ↪[L] N)

def AmalgamableOver (T : L.Theory)
    {A B C : Type (max u v)} [L.Structure A] [L.Structure B] [L.Structure C]
    (i : A ↪[L] B) (j : A ↪[L] C) : Prop :=
  ∃ (N : T.ModelType.{u, v, max u v}) (f : B ↪[L] N) (g : C ↪[L] N),
    f.comp i = g.comp j

-- FirstOrder.Language.Substructure、または独立の構造用述語として置く。
def GeneratedByAtMost (C : Type w) [L.Structure C] (n : ℕ) : Prop :=
  ∃ s : Finset C, s.card ≤ n ∧ Substructure.closure L (s : Set C) = ⊤
```

新 `FiniteInclusion T` は有限な base/ext、両者の `L.Structure`、
`incl : base ↪[L] ext`、`T.Embeddable ext` を束ねる。
`T.Embeddable base` は合成で得られるので追加仮定は不要。
これは「共通の `M₀ ⊨ T` の有限部分構造 `A ⊆ B`」を同型で置き換えたもの。

`BoundedAmalgamationObstructions T` の量化は次の通り。

```text
∀ d : FiniteInclusion T, ∃ n : ℕ,
  ∀ M : T.ModelType, T.IsExistentiallyClosed M →
  ∀ j : d.base ↪[L] M, ¬ T.AmalgamableOver d.incl j →
  ∃ C : L.Substructure M, ∃ hj : ∀ a, j a ∈ C,
    GeneratedByAtMost C n ∧
    ¬ T.AmalgamableOver d.incl (j.codRestrict C hj).
```

終端の予定名は対応表の名称を保つ。

```lean
theorem hasModelCompanion_iff_boundedAmalgamationObstructions
    [Finite L.Symbols] (hLF : T.IsLocallyFinite) (hΠ : T.IsPiTwo) :
    T.HasModelCompanion ↔ T.BoundedAmalgamationObstructions
```

型に保持する条件は次の通り。

- `n` は有限 inclusion `d` ごとに一つ。e.c. モデル `M`、その中の marking `j`、失敗した
  amalgam ごとに選んではならない。
- 上界は `C` の**総生成元数**。原稿 224。旧 `BoundedWitness` の「base に加えて n 個」と
  同一視しない。旧値 `b(d)` からこの型へは `Nat.card d.base + b(d)` で移行できる。
- `A,B,C ⊨ T` を要求しない。一般 Π₂ 理論の部分構造はモデルとは限らない。
  `C` の有限性は `hLF`、生成元の有限性、`C ≤ M ⊨ T` から得る。
- amalgam の二つの写像は embedding。像の交差がちょうど `A` という強い条件は付けない。
- 定数のない一般言語では空の有限部分構造もあり得る。`Nonempty A/B/C` は追加しない。
  `n=0` や空の生成集合を扱うため、固定長 tuple の padding を空構造内で行わない。
- `T` が不充足の場合も statement はそのまま意味を持つ。`T.IsSatisfiable` を追加しない。
- 他の宇宙の `M` に対する e.c./companion bridge は別残件。有限構造の carrier は
  `Fin k` と同型にして canonical universe に移せるが、任意の巨大な `M` については別問題。

## 2. 今ある producer と直接の消費箇所

| 現在の宣言 | 消費箇所 |
| --- | --- |
| [ModelCompanionCriterion.lean:65](/home/ywr/t3-model-companion/T3/ModelTheory/ModelCompanionCriterion.lean:65) `isModelCompanionOf_iff_models_iff_isExistentiallyClosed` | 必要方向で e.c. `M` を `T*` のモデルとする。十分方向で extension scheme のモデル類等式を MC にする。 |
| [ModelCompanionCriterion.lean:43](/home/ywr/t3-model-companion/T3/ModelTheory/ModelCompanionCriterion.lean:43) `isModelCompanionOf_of_isExistentiallyClosed_iff` | 十分方向の二つのモデル類包含をそのまま渡せる終端。 |
| [ExistentiallyClosedExtension.lean:326](/home/ywr/t3-model-companion/T3/ModelTheory/ExistentiallyClosedExtension.lean:326) `exists_isExistentiallyClosed_embedding` | 上記 Fact 2.3 の内部 producer。十分方向で新しく拡大列を作り直す必要はない。 |
| [ModelCompanion.lean:104](/home/ywr/t3-model-companion/T3/ModelTheory/ModelCompanion.lean:104) `IsModelComplete` | 必要方向で `¬ Ext(B/A)` を存在式に変換。既存定義は構文的な同値を返す。 |
| [FiniteDiagram.lean:101](/home/ywr/t3-model-companion/T3/ModelTheory/FiniteDiagram.lean:101), [同:142](/home/ywr/t3-model-companion/T3/ModelTheory/FiniteDiagram.lean:142) `finiteDiagram`, `realize_finiteDiagram_iff` | base の図式。任意有限構造に使用可能。 |
| [FiniteDiagram.lean:353](/home/ywr/t3-model-companion/T3/ModelTheory/FiniteDiagram.lean:353), [同:373](/home/ywr/t3-model-companion/T3/ModelTheory/FiniteDiagram.lean:373) `embeddingExtensionDiagram`, `realize_exists_embeddingExtensionDiagram_iff` | 相対図式 `θ(B/A)` と「B の embedding が A 上延長する」の同値。既に一般言語で完成。 |
| [FiniteDiagram.lean:426](/home/ywr/t3-model-companion/T3/ModelTheory/FiniteDiagram.lean:426) `IsExistentiallyClosed.exists_embedding_over_tuple` | e.c. `M` に対して `AmalgamableOver(B,M;A) ↔ ∃ B ↪ M over A`。有限 `B` にモデル条件は不要。 |
| [UniformLocalFiniteness.lean:182](/home/ywr/t3-model-companion/T3/ModelTheory/UniformLocalFiniteness.lean:182) `exists_card_closure_le_of_isLocallyFinite` | 原稿 251 の `n_{A,B}` から cardinal bound `m_{A,B}` への移行。 |
| [同:89](/home/ywr/t3-model-companion/T3/ModelTheory/UniformLocalFiniteness.lean:89) `IsLocallyFinite.exists_finite_qfType_cover` | 有限 marked extension の有限同型代表族を実際に選ぶ producer に使える。下記 §4。 |
| [同:208](/home/ywr/t3-model-companion/T3/ModelTheory/UniformLocalFiniteness.lean:208) `exists_finite_qf_representatives` | 有限個の QF 型を Boolean 真偽ベクトルで符号化する別入口。有限な禁止式の代表族を得るまでの追加証明は必要。 |
| [FiniteDiagram.lean:298](/home/ywr/t3-model-companion/T3/ModelTheory/FiniteDiagram.lean:298) `realize_finiteGeneratedDiagram_iff` | 同じ QF 型の生成 tuple から生成部分構造間の embedding を作る。有限 marked 型分類の主要部品。 |

## 3. 必要方向を先に閉じる

予定モジュールは `T3.ModelTheory.Amalgamation` と
`T3.ModelTheory.BoundedAmalgamation`。図式は既存 `FiniteDiagram` を使う。

1. `AmalgamableOver` の左右対称性、embedding による restriction、marked equivalence による
   不変性を実装。相対拡大式を
   `Ext(i) := (embeddingExtensionDiagram (L := L) (i : A → B)).iExs B`
   と略記する。`realize_exists_embeddingExtensionDiagram_iff` がその意味を既に与える。
2. `IsExistentiallyClosed.amalgamableOver_iff_exists_embedding` を完成する。
   forward は有限 embedding transfer、reverse は `M` 自身を amalgam に取る。
   要求は有限言語・有限 A/B と e.c. 性だけで、この補題自体に局所有限性は不要。
3. 未実装の構文 helper：`BoundedFormula.IsExistential.exists_qf_matrix`。
   `ψ : L.Formula (Fin a)`、`ψ.IsExistential` から、**ψ のみに依存する** `k` と
   `θ : L.Formula (Fin a ⊕ Fin k)` を返し、`θ.IsQF` と
   `ψ.Realize y ↔ (θ.iExs (Fin k)).Realize y` を全構造・全 assignment で証明する。
   `IsExistential` のコンストラクタは QF と `ex` の二つ
   （mathlib `ModelTheory/Complexity.lean:343`）なので、存在 prefix を再帰的に取り出す。
   既存 `ModelCompleteness.lean:322` は局所的な `k` を返すため、それだけを使って
   全 `M,j` に共通の上界を得たことにしてはならない。
4. `hMC.isModelComplete` を、A を `Fin a` に列挙して得た `¬ Ext(i)` に適用。
   得られた存在式を上の helper で `∃ z, θ(z,y)` にする。ここで `n := k + a` を固定。
   source 234–235 の通り、`n` を選ぶのは `M,j` より先。
5. 非 amalgamability から `M ⊨ ¬ Ext(i)(j)`、Fact 2.3 から `M ⊨ T*`。
   witness `c : Fin k → M` を取り、`C := closure L (range j ∪ range c)`。
   finite ranges の和集合の cardinal bound と closure transport で
   `GeneratedByAtMost C (k+a)` を示す。有限性は `hLF` から得る。
6. 仮に `C,B` の amalgam `N₀ ⊨ T` があれば、`hMC.isCompanion.2` で `N₀ ↪ N ⊨ T*`。
   QF の絶対性により `θ` を `M → C → N₀ → N` の順に移す。
   **最初の矢印は全 M の写像ではない**ので、まず assignment を C に取り直し、
   C の subtype embedding で QF 真偽を反映させる。
   すると N は `¬ Ext(i)` と B のコピーを同時に持ち矛盾する（source 240–243）。

一様 witness helper の別実装は、旧 `ExistentialWitness` の再帰に quantifier 数上界を追加し、
`∃ k, ∀ N y, ψ.Realize y → ∃ s, s.card ≤ k ∧ ...` とするもの。
その場合も bound の `k` は realization より前に量化する。
原稿の QF 行列を明示するには上の matrix API が最も直接的。

## 4. 十分方向：有限禁止族が次の producer

必要な新 API を `FiniteObstructions.lean` にまとめる。
`d : FiniteInclusion T` と総生成元 bound `n` に対して、有限な index `ι`、有限構造 `C k`、
marking `j k : d.base ↪[L] C k` を選ぶ。

```text
exists_finite_bad_extension_family (hLF) (d) (n):
  ∃ finite family (C k, j k),
    (∀ k, T.Embeddable (C k) ∧ GeneratedByAtMost (C k) n ∧
      ¬ T.AmalgamableOver d.incl (j k)) ∧
    ∀ C [L.Structure C] [Finite C] (c : d.base ↪[L] C),
      T.Embeddable C → GeneratedByAtMost C n →
      ¬ T.AmalgamableOver d.incl c →
      ∃ k, ∃ e : C k ≃[L] C, e.toEmbedding.comp (j k) = c.
```

これは unmarked な cardinal bound だけより強い。A の各元を固定する同型が必要。
原稿 246–252 と同じ有限 marked isomorphism type の代表族であり、代表の重複は harmless。

既存 finite-QF-type producer を使う具体的な構成順：

1. `k ≤ n` 個の生成元を実際に列挙し、A の `a := Nat.card A` 個の marked 元を加えた
   `k+a`-tuple を ambient `T`-model 内に取る。長さを k ごとに扱えば空 C への padding は不要。
2. `exists_finite_qfType_cover hLF (k+a)` で、その tuple の QF 型を有限集合で分類。
   `finiteGeneratedDiagram` を両方向に実現すると、生成部分構造間に tuple を対応させる
   embedding ができる。合成は生成 tuple 上恒等なので closure induction で恒等。
   これを `equiv_closure_of_same_qfType` として実装すれば、**marked** 同型が得られる。
3. 各 k と各有限 QF 型について、該当する bad marked extension が存在するときだけ
   そのクラスから代表を一つ選ぶ。代表は元の bad class から取るので、
   `T.Embeddable`・総生成元 bound n・非 amalgamability を保持できる。
   高々 n+1 個の有限族の和を取る。

この方法は原稿の「有限同型型から代表を選ぶ」構成を保ち、群の自由商による符号化を使わない。
Fact 2.5 の cardinal bound をまず使い `Fin m` 上の有限構造表を全列挙する方法も正確だが、
現 API では有限 QF cover の方が既存コードの再利用が多い。
`exists_finite_qf_representatives` や diagram の有限連言だけから、marked bad family が
完成したとは主張しない。上記の同型と代表選択が追加 producer。

## 5. extension scheme と二つのモデル類包含

`ExtensionAxioms.lean` の予定入口は、任意有限 bad family に対する
`extensionAxiom` と `realize_extensionAxiom_iff`。
base 図式 `finiteDiagram A`、相対式 `Ext(i)`、有限族の `¬ Ext(j k)` の連言を使い、
source 255 と同じ文を作る。index は `FiniteInclusion T` に制限する。
原稿末尾の省略記法「A⊆B are finite」を、T に埋め込めない任意の B に拡大しない。

`extensionTheory bound := Set.range (fun d => extensionAxiom ...)`、`T* := T ∪ extensionTheory bound`。

- `models_extensionTheory_of_isExistentiallyClosed`：copy A in M に対して場合分け。
  amalgam があれば `exists_embedding_over_tuple` で B を M に戻す。
  なければ bounded obstruction が C を供給し、有限 bad family の completeness で
  禁止 C のコピーが M にあることになり antecedent と矛盾。
  **bounded hypothesis を使うのはこの包含だけ**（source 257 の省略された一段）。
- `isExistentiallyClosed_of_models_extensionTheory`：存在式の有限 witness を取り、
  `A := closure(parameters) ≤ M`、`B := closure(witnesses ∪ f(A)) ≤ N ⊨ T`。
  hLF により有限。禁止 C のコピーが M にあれば、f と合成して N が C/B の amalgam になる。
  従って scheme が B のコピーを M に与え、witness をその embedding で移す。
  この包含は bound の正しさを使わず、各禁止族の soundness だけを使う。
- 最後に Fact 2.3 の `isModelCompanionOf_of_isExistentiallyClosed_iff hΠ` を適用する。
  `T*` のモデルから `T` のモデルへの移行は `T ⊆ T*` による。
  A/B/C についてその移行を行ってはならない。

存在式の有限 witness は旧ファイルをほぼそのまま再利用できる。
QF 行列 helper を先に実装した場合はその witness tuple でもよい。
既存 finite embedding transfer は e.c.→scheme 側で使い、
scheme→e.c. 側で未証明の e.c. 性を仮定して使わない。

## 6. 旧コードの再利用範囲

Yawara Ishida による以前の形式化から、以下の一般モデル理論の宣言・証明を read-only で確認した。
新 repo に既に移植済みという意味ではない。

| 旧実装の数学的内容 | 再利用と必要な変更 |
| --- | --- |
| 相対図式 | relative diagram は新 `embeddingExtensionDiagram` が既に一般化済み。重複定義は不要。 |
| 拡大公理の構成と実現条件 | `Language.group` と `groupDiagram` を L と `finiteDiagram` に変更。証明の Boolean/quantifier 部分は再利用可能。 |
| 有限部分構造内の存在式の証人 | mathlib のみの一般言語定理。import/doc locator を更新して直接再利用可能。旧結果は有限性だけで uniform cardinal bound を返さない。 |
| 禁止拡大の有限列挙 | `BadIndex` は有限な `MarkedFree A n` の normal subgroup、completeness は marked quotient。一般 T にその自由構造はないため、§4 の finite marked type producer に置換する。 |
| 有限包含と有界障害 | `FiniteInclusion`・`BoundedWitness` は群/T₃特化。構造の realizability と総生成元数へ変更する。 |
| 二つのモデル類の包含 | 二つのモデル類包含の proof body は原稿と同じ。group/subgroup の変換を L-embedding/substructure API に置換する。 |
| 有界障害から model companion への十分方向 | 旧終端は T₃ の十分方向のみ。一般 Π₂ の終端は現在の Fact 2.3 を使う。 |
| amalgam の合成・同型輸送 | amalgam の合成・同型輸送の発想を再利用。定義本体の `Type 0`、群、指数3条件は移植しない。 |

旧実装の有限 subamalgam への置換説明は一般 Π₂ T には使えない。
有限生成部分構造を取り直すと T のモデルでなくなる場合がある。
新 amalgam は最初から canonical universe の `N : T.ModelType` とし、宇宙拡張は別途扱う。

## 7. 実装順と完了の境界

1. `Amalgamation`：一般 T の embedding-based amalgam、marked transport、e.c. と有限拡大式の同値。
2. `ExistentialWitness`：旧一般 helper の再利用と、必要方向用の一様 QF matrix。
3. `BoundedAmalgamation` の必要方向：原稿 233–243 を総生成元上界付きで完成。
4. `FiniteObstructions`：同じ QF 型から marked generated structure の同型、有限 bad family。
5. `ExtensionAxioms`：任意有限言語・任意有限 forbidden family の文と realization iff。
6. scheme の二つの包含、Fact 2.3 接続、予定の全 iff を公開。
7. 別作業として T₃ の Π₂/局所有限性と群論的 bounded witness を新述語へ接続。

3 と 4–5 は 1–2 完了後に独立に進められる。3 の必要方向が完成しても Fact 2.6 全体は partial。
有限 family の存在だけでも十分方向は完成ではなく、二つの包含と終端を型で閉じる必要がある。
この note 作成時点では Fact 2.6 本体は未実装。数学コードの build/lint の新規検証は行っていない。

> 公開履歴の整理に伴い、非公開の作業場所・内部識別子を省略した。数学的記述と当時の検証結果は保持しており、ここに記す検証は当時の対象に限る。
