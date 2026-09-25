# Fact 2.6 の実装 frontier

> 履歴資料（v4 原稿）。原稿は [archives/T3_modelcompanion_v4.tex](../archives/T3_modelcompanion_v4.tex) に保存。以下の番号・行・検証結果は当時のもの。
> 現行 v9 の対応は [対応表](../docs/paper-map.md) と [v9 移行記録](v9-migration.md) を参照。

2026-09-10。本稿は作成時点の実装済み定理と次に作る API を区別した設計記録。
現在の実装・検証状況は [論文対応表](../docs/paper-map.md) を参照する。
Paper-ID: `model_theory.bounded_amalgamation_criterion`。
原稿は [T3_modelcompanion_v4.tex](../archives/T3_modelcompanion_v4.tex)、
label `fact:locally finiteness and model companion`、statement 214–228、proof 230–263。
source SHA256: `79745dfa1660a827c51ec3c6b2006ee9d6243cb4702f97a75e5b55357b89f50b`。

**次のまとまった終端は一般の必要方向 `MC ⇒ bounded obstruction`。**
そのために新たな compactness 証明は不要であり、有限相対図式、存在式の一様な有限 witness、
amalgam の合成を接続すればよい。十分方向は一般言語の extension scheme を構成し、
禁止拡大の有限代表族を供給するのが主な未実装部分。

[数学的監査](paper-mathematical-audit.md) には原稿の数学的確認がある。
本 note はその説明を繰り返さず、作成時点の API からの接続を記す。
Fact 2.3 はこの設計記録の前提として完成している。

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
- 上界は `C` の**総生成元数**。原稿 224。base の生成元もこの上界に含める。
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
| [ModelCompanionCriterion.lean](../T3/ModelTheory/ModelCompanionCriterion.lean) `isModelCompanionOf_iff_models_iff_isExistentiallyClosed` | 必要方向で e.c. `M` を `T*` のモデルとする。十分方向で extension scheme のモデル類等式を MC にする。 |
| [ModelCompanionCriterion.lean](../T3/ModelTheory/ModelCompanionCriterion.lean) `isModelCompanionOf_of_isExistentiallyClosed_iff` | 十分方向の二つのモデル類包含をそのまま渡せる終端。 |
| [ExistentiallyClosedExtension.lean](../T3/ModelTheory/ExistentiallyClosedExtension.lean) `exists_isExistentiallyClosed_embedding` | 上記 Fact 2.3 の内部 producer。十分方向で新しく拡大列を作り直す必要はない。 |
| [ModelCompanion.lean](../T3/ModelTheory/ModelCompanion.lean) `IsModelComplete` | 必要方向で `¬ Ext(B/A)` を存在式に変換。既存定義は構文的な同値を返す。 |
| [FiniteDiagram.lean](../T3/ModelTheory/FiniteDiagram.lean) `finiteDiagram`, `realize_finiteDiagram_iff` | base の図式。任意有限構造に使用可能。 |
| [FiniteDiagram.lean](../T3/ModelTheory/FiniteDiagram.lean) `embeddingExtensionDiagram`, `realize_exists_embeddingExtensionDiagram_iff` | 相対図式 `θ(B/A)` と「B の embedding が A 上延長する」の同値。既に一般言語で完成。 |
| [FiniteDiagram.lean](../T3/ModelTheory/FiniteDiagram.lean) `IsExistentiallyClosed.exists_embedding_over_tuple` | e.c. `M` に対して `AmalgamableOver(B,M;A) ↔ ∃ B ↪ M over A`。有限 `B` にモデル条件は不要。 |
| [UniformLocalFiniteness.lean](../T3/ModelTheory/UniformLocalFiniteness.lean) `exists_card_closure_le_of_isLocallyFinite` | 原稿 251 の `n_{A,B}` から cardinal bound `m_{A,B}` への移行。 |
| [UniformLocalFiniteness.lean](../T3/ModelTheory/UniformLocalFiniteness.lean) `IsLocallyFinite.exists_finite_qfType_cover` | 有限 marked extension の有限同型代表族を実際に選ぶ producer に使える。下記 §4。 |
| [UniformLocalFiniteness.lean](../T3/ModelTheory/UniformLocalFiniteness.lean) `exists_finite_qf_representatives` | 有限個の QF 型を Boolean 真偽ベクトルで符号化する別入口。有限な禁止式の代表族を得るまでの追加証明は必要。 |
| [FiniteDiagram.lean](../T3/ModelTheory/FiniteDiagram.lean) `realize_finiteGeneratedDiagram_iff` | 同じ QF 型の生成 tuple から生成部分構造間の embedding を作る。有限 marked 型分類の主要部品。 |

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

一様 witness helper の別実装は、存在式の再帰に沿って quantifier 数上界を証明し、
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
作成時点の API では有限 QF cover から直接接続できる。
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

存在式の有限 witness は構文に関する帰納法で得る。
QF 行列 helper を先に実装した場合はその witness tuple でもよい。
既存 finite embedding transfer は e.c.→scheme 側で使い、
scheme→e.c. 側で未証明の e.c. 性を仮定して使わない。

## 6. 対応する数学モジュール

この設計に対応する現在のモジュールは次のとおり。当時の予定 API と現在の検証状況は
[論文対応表](../docs/paper-map.md) で区別する。

| モジュール | 数学的な役割 |
| --- | --- |
| [Amalgamation.lean](../T3/ModelTheory/Amalgamation.lean) | 一般言語の embedding による amalgam と有限拡大式。 |
| [ExistentialWitness.lean](../T3/ModelTheory/ExistentialWitness.lean) | モデルの選択に先立つ存在式の一様有限 witness 上界。 |
| [BoundedAmalgamation.lean](../T3/ModelTheory/BoundedAmalgamation.lean) | 総生成元数による有界障害と必要方向。 |
| [FiniteObstructions.lean](../T3/ModelTheory/FiniteObstructions.lean) | base を固定する有限 marked 障害の代表族。 |
| [ExtensionAxioms.lean](../T3/ModelTheory/ExtensionAxioms.lean) | 一般有限言語の extension sentence と実現条件。 |
| [BoundedAmalgamationCriterion.lean](../T3/ModelTheory/BoundedAmalgamationCriterion.lean) | extension scheme のモデル類と一般 criterion の両方向。 |

一般 Π₂ 理論では、amalgam を有限部分構造に置き換えるだけでは足りない。
有限生成部分構造を取り直すと T のモデルでなくなる場合がある。
この設計の amalgam は canonical universe の `N : T.ModelType` とし、宇宙拡張は別途扱う。

## 7. 実装順と完了の境界

1. `Amalgamation`：一般 T の embedding-based amalgam、marked transport、e.c. と有限拡大式の同値。
2. `ExistentialWitness`：一様な有限 witness 上界と、必要方向用の一様 QF matrix。
3. `BoundedAmalgamation` の必要方向：原稿 233–243 を総生成元上界付きで完成。
4. `FiniteObstructions`：同じ QF 型から marked generated structure の同型、有限 bad family。
5. `ExtensionAxioms`：任意有限言語・任意有限 forbidden family の文と realization iff。
6. scheme の二つの包含、Fact 2.3 接続、予定の全 iff を公開。
7. 別作業として T₃ の Π₂/局所有限性と群論的 bounded witness を新述語へ接続。

3 と 4–5 は 1–2 完了後に独立に進められる。3 の必要方向が完成しても Fact 2.6 全体は partial。
有限 family の存在だけでも十分方向は完成ではなく、二つの包含と終端を型で閉じる必要がある。
この note 作成時点では Fact 2.6 本体は未実装。数学コードの build/lint の新規検証は行っていない。
