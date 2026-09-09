# T3_modelcompanion_v4.tex と既存 Lean の対応監査

> Historical T3 revision identifiers have been omitted for publication. Recorded commands, outcomes, and source hashes describe the original checks; this edited record does not certify the rewritten historical snapshots.

監査日: 2026-09-09。判定: **最終的な存在結論は既存 Lean にあるが、v4 論文全体の paper-faithful な形式化は未完了。**

後続の [数学的検証](/home/ywr/t3-model-companion/notes/paper-mathematical-audit.md) では、v4 自体の論証・定数を独立に確認した。以下の fidelity の不足は、論文の数学的誤りを意味しない。

この監査でいう faithful は、同じ最終結論だけでなく、定義、量化範囲、定数、補題の主張、主要な証明手順が対応することを要求する。同値な符号化や省略補題の展開は許容するが、その対応も記録・証明する。既存の粗い上界や別構成で最終結論を得たことを、論文のより強い中間定理の証明とは数えない。

## 対象と再現情報

- 一次資料: [T3_modelcompanion_v4.tex](/home/ywr/t3-model-companion/T3_modelcompanion_v4.tex)。著者 Yawara Ishida, Ryosuke Mizuno, Kota Takeuchi、表題 *Existence of a Model Companion for Groups of Exponent 3*。1309 行。
- TeX SHA256: `79745dfa1660a827c51ec3c6b2006ee9d6243cb4702f97a75e5b55357b89f50b`。
- 新リポジトリ HEAD: `[historical revision omitted]`。監査開始時には TeX/PDF は未追跡で、Lean project 設定はまだない。
- 比較対象は Yawara Ishida による以前の指数 3 群の形式化。
- 旧自然言語証明と既存 Lean の文書内の節番号は旧稿を指し、TeX v4 の節番号ではない。
- 旧レビューの対象は旧自然言語証明であり、この TeX v4 ではない。
- 本監査では比較対象の数学ソースを編集していない。

表中の TeX 行番号はすべて上記ハッシュのファイル。「既存 Lean」「旧実装」は上記の以前の指数 3 群の形式化を指す。検索結果だけで同一性を判定せず、主な候補の型と証明本体、旧自然言語証明を照合した。以下の「未実装」は対応する一般 statement/API が今回の実装調査で見つからなかったという意味であり、既存補題から導出不可能という意味ではない。

## 最終結論と証明経路

TeX 743–745 の系「T₃ は model companion をもつ」に対応する最終定理は既存 Lean にある。型に追加の数学的仮定はなく、結論は指数 3 群の理論が model companion をもつことである。

大きな流れは両者で共通する。

1. 指数 3 自由群の正規形と exterior coordinates を用意する。
2. commutator roots と triple-commutator roots を付加する。
3. 有限部分群を strict に拡大し、有限図式と e.c. 性で元のモデルに戻す。
4. 非 amalgamation を pushout の非自明な kernel 元で検出する。
5. 共役圧縮で有限 support を取り、strict coproduct の単射性で certificate を移送する。
6. 有限禁止図式による extension axioms から model companion を得る。

ただし、2–3 の構成・定量評価、5 の一般性、6 の一般モデル理論部分には以下の差がある。

## 決定的な差分

### D1. 支持補題が生成元数ではなく群の位数を使っている

一次資料は TeX 668–692。`d(B) ≤ m`、`|Δ| ≤ n` から **`d(C) ≤ 3(m+1)n`** を得る。証明は B の生成元 `b_j` ごとに交差交換子をまとめる。

対して旧実装の支持補題は `Nat.card BB + 1` 個の support 元を与える。実際に BB の像の全要素を列挙する。旧実装の certificate 構成はその結果を使い、`3 * Fintype.card A * (Nat.card BB + 1)` を得る。

共役幅 3 自体と「γ₃ を除いて collect する」構造は対応する。しかし `|B|` を `d(B)` に読み替えることはできない。原稿どおりの生成元列を使う collect 補題と support bound が必要。

旧自然言語証明は B/B′ を張る s 個の元による `5r(s+1)+1` を使っていた。Lean は共役幅を 5 から 3 に改善した一方、s を位数へ粗くしている。旧自然言語証明と Lean も定数まで同一ではない。

### D2. Proposition A の最終供給元 `15n²` は未形式化

一次資料は TeX 1076–1107、1133–1174、1212–1251。論文は次の次元評価を順に使う。

- `(C ∩ γ₂(G))/γ₂(C)` の基底を取り、追加生成元は `2n` 個以下。
- 第 1 段階後の次数 2 の次元から、追加生成元は `3·binom(3n,2)` 個以下。
- 非自明群に F₂ を coproduct して、さらに 2 個を加える。
- 得られる D は `d(D) ≤ 15n²` に加え、**D 自身の上下中心列が逆順に一致する**。

対して旧実装の strict extension の上界は、`λ(n)=n+binom(n,2)+binom(n,3)` として

```text
b(n) = n + 2·3^λ(n) + 3·3^λ(n + 2·3^λ(n))
s(n) = b(n) + 3
```

である。実装は基底ではなく有限部分群の全要素を列挙する。例えば旧実装の `s(1)=10+3^64` に対し論文は 15 である。これは既存 bound の違いを示すものであり、15 が不可能という主張ではない。

旧実装の strict envelope の構成は F₃ を使う。その証明内では内部中心列の一致を使うが、返り値は strictness の二条件で、論文の内部中心列一致まで含めた定理として公開されていない。

旧自然言語証明の bound も `n+2λ(n)+3λ(n+2λ(n))+3` であり、TeX v4、旧自然言語証明、Lean の三者は異なる。必要な作業は v4 の基底選択・次元 bound と F₂ 構成を証明し、完全な結論を保持して e.c. 転送すること。

### D3. F₂ による安定化と一般 coproduct の定理が不足

TeX 962–1001 は **任意の非自明な G** と F₂ について strict inclusion と内部中心列一致を証明する。旧実装の coproduct の中心列の結果は **有限 C** と F₃ の定理である。F₂ への変更は単なる変数置換ではない。論文は G の非自明な abelianization 成分と F₂ の混合 block を使い、F₃ 実装は自由因子に 3 つの座標を持つことを使う。

さらに TeX 946–958 の strict coproduct 補題は D、G、B を有限に限定しない。旧実装の coproduct 比較の抽象 API は `[Finite B]` と `[Finite D]` を要求する。無限 ambient を扱う版も、ambient の補基底を無限にするものであり、有限 X,U の仮定は残る。

有限 D,B は主定理の消費箇所には十分だが、v4 の一般補題全体の形式化ではない。論文の graded coproduct の自然性と injectivity を通る一般証明が必要。

### D4. graded Lie algebra と自然な同型の API が未完成

TeX 266–320、391–499、550–641、843–928 では、`gr(G)` を graded Lie algebra として扱い、`gr(f)`、strictness との同値、quotient formula、coproduct の tensor block 同型を証明する。

旧実装の graded coordinates は有限 rank の次数別の `MulEquiv` を与え、bracket の一部に対応する wedge action もある。これらは重要な再利用資産であり、F₃ 上の加法群としての符号化そのものが誤りということではない。

しかし、旧実装には `LieRing`、`LieAlgebra`、`LieEquiv`、`DirectSum`、`TensorProduct` による対応 API が見つからない。論文の次の statement は既存結果を束ねるだけで「既にある」とは扱えない。

- `Λ^[1,3] V` の Lie algebra 構造と Jacobi。
- 任意の指数 3 群の associated graded、誘導写像と bracket。
- `gr(f)` の単射性から f の単射性、および strictness の同値。
- `gr_i(G/N) ≅ gr_i(G)/gr_i^G(N)`。
- 任意の G₀,G₁ の coproduct に対する η₁,η₂,η₃ の tensor/direct-sum 同型と block bracket。
- 無限 rank の associated graded と exterior algebra の同型。

既存は有限段階の座標と kernel intersection を直接追跡して主定理に必要な単射性を得ている。新形式化では論文の statement を先に定め、既存の座標補題をそれらの証明に接続する必要がある。

### D5. 主定理の公開 statement と明示式が違う

TeX 704–739 は `d(B) ≤ m` **だけ**に依存する一つの関数 f により、障害部分群 D の**総生成元数**を抑える。その証明で

```text
f(m) = f₀((3m+4)t(m)+1),   t(m)=m+binom(m,2)+binom(m,3)
```

を選ぶ。

旧実装の有界 witness の構成は有限包含 d ごとに

```text
witnessBound s d = s (|A| + 3|A|(|B|+1) + 1)
```

を選び、旧実装の有界 witness の公開述語は A 全体に**追加する生成元数**を bound する。構成内部の補助結果は総生成元数も与えるので、情報が全くないわけではない。しかし最後の API はそれより弱い形に包む。

位数評価と単調性から粗い rank-only 存在定理をさらに導く余地はあるが、それは今回まだ形式化しておらず、v4 の明示式・生成元ベースの証明とは別に確認すべきもの。D1–D3 を解消した上で v4 の主定理をその型で公開する必要がある。

### D6. モデル理論の一般的な背景事実は特殊化のみ

TeX 178–201 は model completeness を existential formula への書換えで定義し、Π₂ 理論一般について e.c. models と model companion の models の同値を述べる。旧実装は全 embedding の elementary 性で model completeness を定義し、e.c. も定義する。標準的に対応する定義だが、構文的・意味論的 model completeness の同値 bridge は今回の既存実装調査で見つからない。

TeX 203–263 は有限言語の locally finite Π₂ 理論一般について、有界非 amalgamation 障害と model companion の**同値**を証明する。既存は universal theory の e.c. class の公理化から model companion を得る結果と、指数 3 に特殊化した **bounded witness ⇒ model companion** を持つ。**model companion の存在 ⇒ bounded witness** の必要方向、および一般 Π₂/local finiteness の定理は未実装。一方、universal theory について「model companion のモデル ⇒ e.c.」は旧実装に存在する。

一方、有限禁止図式による sufficiency の証明はよく対応する。旧実装は有限図式、禁止拡大の有限列挙、e.c. と extension scheme の同値を実装している。

## 論文の残りの主要項目との対応表

「対応」は主張または明記した数学的部分の対応であり、証明全行の完全一致を認証するラベルではない。

| TeX 行 / 項目 | 既存 Lean の入口 | 判定と残作業 |
| --- | --- | --- |
| 136–172: T₃、free exponent-three group、coproduct | 指数 3 の基本対象 | 基本対象は対応。指数は「3 を割る」。 |
| 326–372: 中心列、Engel、四重交換子消滅、基本恒等式 | 中心列と基本恒等式 | 主な群論的基礎は対応。Lean の `lowerCentralSeries 2` が論文の γ₃ に対応する。 |
| 378–389: coproduct の各因子の単射性 | coproduct の因子の単射性 | retraction による kernel 計算と quotient map の単射性が対応。 |
| 510–520: 内部中心列一致から strictness | 内部中心列一致から strictness | e.c. ambient への適用に必要な形を持つ。論文の任意 ambient での一般 statement は別途公開が必要。 |
| 525–547: Levi–van der Waerden 正規形と位数 | 有限 rank の正規形と位数 | 有限 rank の正規形・位数を実証済み。無限 rank は各消費者で有限段階へ還元。一般の有限支持正規形の公開 statement は別途整える。 |
| 653–665: 共役幅 3 | 共役幅 3 | E_a 型の部分群を作り指数を mod 3 に落とす証明が対応。Lean は逆向きの共役 `g*a*g⁻¹` を使うが g↦g⁻¹ で同じ集合。 |
| 759–799: abelianization の基底 lift | abelianization の基底 lift | 基底 lift が生成し kernel が derived に入る内容を持つ。任意の指定済み基底/代表元の statement との bridge は整える。 |
| 802–840: normal closure L=K[K,G] と graded image | normal closure と graded image | 群としての等式は対応。graded image は有限自由群の exterior readout で実装し、論文の任意 G に対する三項一組の statement は未公開。 |
| 1010–1073: 有限族への同時 commutator root | commutator root の付加 | 一つの root について次数 2・3 の分離を実装。論文の F₂ₙ を用いる同時 quotient と、その単射性の statement は未実装。 |
| 1076–1107: 2m 個以下で derived strict 化 | derived strict 化 | 与えた list の長さの 2 倍の bound はある。論文の quotient basis の選択と長さ ≤m は未実装。D2。 |
| 1110–1129: 中心元の有限族への同時 triple root | 中心元への triple root の付加 | 一つの中心元を G×F₃ の quotient で処理。複数は逐次適用し、論文の G×F₃ₙ の一括 quotient は未実装。 |
| 1133–1174: 3·binom(n,2) 個で γ₃ strict 化 | γ₃ strict 化 | list の長さの 3 倍で逐次処理する。dimension bound と一括 quotient 証明は未実装。D2。 |
| 1177–1182: triple roots の共有による最適化の remark | 直接対応する API なし | 4 生成元で 4 つの triple coordinates を使う refinement は現行逐次 F₃ 構成に含まれない。主定理には不要。 |
| 1185–1207: e.c. 群の内部中心列と単一交換子表示 | e.c. 群の中心列 | 結論は対応。ただし Z=γ₃ は中心元へ triple root を付加して e.c. を使う証明で、v4 の F₂ と graded block による証明とは異なる。 |
| 743–745: model companion の存在 | model companion の存在 | 既存の最終定理。完全な v4 形式化とは区別する。 |

TeX 125–130、1258–1271 には Introduction、Applications、Further questions、謝辞の執筆用 placeholder がある。数学的定理の欠落や Lean の `sorry` とは区別する。この監査は文献中の未引用の歴史的主張や論文全体の独立した数学的査読を完了したとの主張でもない。

## 機械検証と mathlib lint 水準

旧実装の Lean/mathlib は v4.32.2。mathlib commit は `905b95818eb32af7874a58b427f50c1711a5e96c`。指数 3 群の最終定理の project 内の推移的 import は **66 モジュール / 17814 行**。対象ソース 66 ファイルのハッシュと対象 revision は検証前後で不変だった。

| 実施した検査 | 結果 |
| --- | --- |
| 旧実装の指数 3 群の最終定理を対象とする通常の `lake build` | exit 0、1982 jobs、warning 0。最新と判定されたキャッシュを利用する通常 build。 |
| 終端定理・strict-extension の存在結果・主要定義計 6 件の公理 allowlist | exit 0。`propext`, `Classical.choice`, `Quot.sound` のみ。 |
| 同じ終端の import 環境に対する `lake lint -- --no-build` | exit 0。import 済み project 全体の environment lint、slow checks を含む。 |
| 対象 66 ファイルを明示列挙した mathlib text/module-name lint | exit 0、違反 0。例外リストは空。 |

当時の project 設定は `autoImplicit=false`、`maxSynthPendingDepth=3`、`weak.linter.mathlibStandardSet=true`、header 有効、longFile=1500。対象内の最大ファイルは 1338 行で、局所的な syntax linter 無効化はない。ソース検査でも `sorry`/`admit`、独自 Lean 公理、`unsafe` 宣言、`native_decide`、`implemented_by` は見つからなかった。

ただし **旧実装の群構造の解釈部分に `@[nolint unusedArguments]` が 1 件ある**。モデルから群構造への API に model instance を残すためと、その場に理由が書かれている。当時の標準 environment lint はこの例外を尊重して通過している。新 repo で例外を一切認めない水準を採る場合は、この API を見直す対象になる。

判定できるのは **使用中の mathlib が下流 project に推奨する標準 lint への準拠**である。`Mathlib/Init.lean:74` は下流向けの標準集合を定義し、mathlib 自身のための `checkInitImports` / `allScriptsDocumented` を除外している。Python style 検査も下流では未対応と文書化されている（`Mathlib/Tactic/Linter/TextBased.lean:504–508`）。全 optional/nightly lint や mathlib 本体専用 CI まで実行したという意味ではない。

以上は当時の対象について記録された検証結果の要約である。比較対象に固有の実行用 probe、出力ログ、import 一覧、ソース manifest は公開履歴に含めていない。この要約は新規の再検証や対象外の全体検査を行ったという主張ではない。

## 分類と形式化方針

今回の trigger は「v4 への完全な faithful 性が未検証」という依頼。一次資料・旧 prose・Lean を比較した D1–D6 は、**statement/API の不一致、定数の粗化、証明経路の差、未形式化部分**として確定した。これらから論文に genuine gap があるという S4 判定は導かれない。

新形式化の対象を v4 と固定するなら、既存の別構成を事後的に「承認済み adaptation」として採用せず、v4 の statement と証明経路へ合わせる。既存の同値表現の不足は bridge として明示し、省略された標準補題は使用箇所とともに展開する。数学的な誤りの候補を新たに見つけた場合は、一次資料の前後と仮定を再確認してから別途分類する。

実装順は次が自然である。

1. 新 repo に mathlib 標準の project/lint 設定と公理検査を置き、論文の各項目と declaration の対応表を維持する。
2. 群論基礎・自由群・正規形の検証済み部分を必要な依存だけ移す。一般モデル理論の補題も、論文の量化範囲と定義 bridge を明示する。
3. associated graded、truncated exterior Lie algebra、quotient と block decomposition を論文の順に構成する。
4. 一般 coproduct の η₁–η₃ と自然性、strict coproduct、非自明 G と F₂ の中心列一致を証明する。
5. simultaneous roots と quotient basis の次元 bound を証明し、完全な内部中心列一致と `15n²` をもつ Proposition A を得る。
6. 生成元数による `3(m+1)n` の support、v4 の明示 f(m)、一般 criterion と存在の系を接続する。

これは次の実装のための監査結果である。今回新しい数学的定理の実装や既存ソースの移植は行っていない。

> 公開履歴の整理に伴い、非公開の作業場所・内部識別子を省略した。数学的記述と当時の検証結果は保持しており、ここに記す検証は当時の対象に限る。
