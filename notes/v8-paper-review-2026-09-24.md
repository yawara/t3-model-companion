# v8 論文の再レビュー（序論・参考文献の原典照合を含む）

確認日: 2026-09-24。同日の [参考文献再レビュー](v8-reference-review-2026-09-24.md) の後に、
論文全体をあらためて見直した記録である。対象は `T3_modelcompanion_v8.tex`、SHA-256
`9546045ccd5cb0170ac54fe1485d356765400ed938c57442da558c41c51fa38c`。以下の行番号はこの
ファイルに対応する。TeX・PDF・Lean は変更していない。

## 範囲と方法

- 序論（127–215行）と abstract の各文を、原典で照合した。原典は `references/` の出版版 PDF と
  そのページ画像、Crossref の書誌記録、arXiv の版情報である。表示本文が引用する 12 文献と、
  文献リストの 13 件すべてを対象にした。
- §2–§5 の証明を手で再計算した。
- TeX を一時ディレクトリでコンパイルした（pdfTeX 3.141592653-2.6-1.40.25、TeX Live 2023）。
  2 回目の実行で、警告・overfull・underfull はいずれも 0 件、21 頁だった。
- 保存した証拠と所在は [証拠の保存先](audit-artifacts/2026-09-24/v8-paper-review/README.md) と
  [照合一覧](audit-artifacts/2026-09-24/v8-paper-review/source-inventory.json) にある。
- 範囲外: 引用文献の全証明の再検証、主定理の再証明、Lean の再監査。新規性の文献調査は網羅的ではない。

## 結論

§2–§5 の数学に誤りは見つからなかった。序論と参考文献には直すべき点が残る。
前回（2026-09-23 と同日午前）のレビューで挙がっていなかったものに「新規」と記す。

## 1. 修正が必要な点

### 1-1. 133行: Eklof–Fischer への帰属（前回の指摘を再確認。著者名の表記は新規）

原稿は「inductive で JEP をもつアーベル群の理論は model companion をもつ」を
Eklof–Fischer (1972) に帰属している。p.116 の節ごとの要約を含めて原著を見直した。
model companion、JEP、inductive を扱う定理はない（§0–§5 は飽和群、初等同値、決定可能性、
拡大言語での量化記号消去、Dedekind 環上の加群）。

主張そのものは正しい。Eklof 単著 *Some model theory of abelian groups*, JSL 37 (1972) の
Theorem 4（p.336）と Theorem 7（pp.339–340）から導ける。導出を独立にやり直した。

1. JEP とコンパクト性から、T と整合的な存在文をすべて満たす T のモデル A がとれる。
   このとき `Th_∀(A) = T_∀`。
2. 各素数 p について `d_{p,n} = dim p^n A[p]`（有限値または ∞）を考える。
   - `D(p;A) = ∞` なら `C_p = Z(p^∞)^{(ω)}` とする。
   - `D(p;A) = d < ∞` なら、`d_{p,n}` が最初に有限になる n を `n_0` とする。
     `n_0 ≥ 1` なら `Z(p^{n_0})^{(ω)}` を置く。各 `n ≥ n_0` について `Z(p^{n+1})` を
     `d_{p,n} − d_{p,n+1}` 個加え、最後に `Z(p^∞)` を d 個加える。
     `d_{p,n}` はいずれ定数 d になるので、差分が 0 でない n は有限個しかなく、巡回成分の位数は有界である。
     このとき `k < n_0` では `dim p^k C_p[p] = ∞`、`k ≥ n_0` では `dim p^k C_p[p] = d_{p,k}` となる。
3. 指数が無限なら `C = ⊕_p C_p ⊕ Q^{(ω)}`、有限なら `C = ⊕_p C_p` とする。
   このとき dim p^n C[p] と指数の有限性は A と一致するので、Theorem 4 により
   `Th_∀(C) = Th_∀(A)` となる。
4. C は Theorem 7(b) の条件を満たす。(i) は D が無限なら巡回成分がないこと、(ii) は無限重複度が
   最下位の位数だけであること、(iii) は Tf = 0 であることから従う。
   よって Theorem 7 により Th(C) は model complete で、Th(C) は T の model companion である。

この議論に inductive の仮定は使わない。v8 の定義（companion かつ model complete）では、
JEP だけで足りる。修正は次のどちらか。

```tex
More generally, every inductive theory of abelian groups with the joint embedding property has a
model companion; this follows from Eklof's description of universal equivalence and of the
model-complete complete theories of abelian groups~\cite[Theorems~4 and~7]{Eklof1972}.
```

(a) 上の文にして、導出の概略を脚注に付ける。(b) この一文を削る。

**新規（著者名）:** EF1972 を文献に残すなら、共著者名は **Fisher** が正しい。
- 表題頁（p.115）の byline は「Edward R. FISCHER」だが、p.116 の柱は「E.R. Fisher」。
- Eklof 単著の文献欄も「E. FISHER」、Fisher 自身の LNM 616 の論文も「Edward R. Fisher」。
- Crossref の記録は byline の誤植をそのまま引き継いでいる。
- v8 の本文（133行）と文献欄（1576行）はどちらも「Fischer」になっている。

### 1-2. 183行: Ivanov の引用（階数は既出。帰属は新規）

- 階数 1 の `B(1,p)` は位数 p の巡回群なので、「rank at least two」が必要である（既出）。
- **新規:** 素数（奇数）指数の場合の一次出典は Ivanov ではない。
  - Novikov–Adian (1968) Part I, p.209 の Theorem: 任意の `m ≥ 2` と奇数 `n ≥ 4381` について、
    m 生成で `x^n = 1` をみたす無限群が存在する（ページ画像で確認）。
  - Adian (1979) が奇数 `n ≥ 665` に改良した。
  - Ivanov 1992 自身が p.258 で「odd divisor not less than 665 をもつ指数では否定的に解決。
    これは Novikov と Adian の定理の easy corollary」と書いている。Ivanov の寄与は偶数指数である。
- Ivanov の Theorem A（`n ≥ 2^48`）も十分大きい素数の主張は含むので、現状の引用は誤りではない。
  ただし業績の帰属として不適切である。

```tex
The free Burnside groups $B(m,p)$ of rank $m\ge2$ are infinite for every prime
$p\ge 4381$~\cite{NovikovAdian1968}, and in fact for every odd exponent at least
$665$~\cite{Adian1979}, so this shows the conjecture for all sufficiently large primes.
```

Ivanov1992 を他で使わないなら削除してよい。残すなら DOI `10.1090/S0273-0979-1992-00305-1` を付ける。
182行の「T_p に model companion がない」は著者らの別稿の予告であり、この照合の対象外である。

### 1-3. 201行: 論理の向きが逆（新規）

「Hence a witness in the smaller coproduct remains a witness in the larger one.」

- この向き（D∗B での証拠が M∗B でも証拠になる）は、任意の準同型について成り立つ。単射性は要らない。
- Theorem 3.3 の証明（797–823行）で使うのは逆の向きである。
  - M∗B の中で見つけた証拠は、有界な部分群 H₀ ⊆ ⟨D, B⟩ の中にある。
  - D∗B → M∗B が単射なので、それが D∗B での証拠になる。

```tex
Hence a witness to the failure of amalgamation that is found in $M*_{\mathcal V_3}B$ and involves
only elements of $D$ and $B$ is already a witness in $D*_{\mathcal V_3}B$.
```

### 1-4. 151行と先行研究の欠落（新規）

151行は「no general result is known that describes the boundary」と書いている。
これに関わる一般的な存在定理がある。

- Burris–Werner (1979, §8) と Burris (1984, Theorem 1.1, p.69) は、有限個の有限構造が生成する
  universal Horn class `ISP(K)` はつねに model companion をもつ、と示している。
  Burris は p.74 の Example (2) で群（有限非可換単純群 G の `ISP(G)`）も扱っている。
- この定理は 𝒱₃ には適用できない。
  - 𝒱₃ は位数に上限のない有限の subdirectly irreducible 群を含む（指数 3 の extraspecial 群
    `3^{1+2k}`。中心は位数 3 で、それが唯一の極小正規部分群になる）。
  - 一方、`ISP(K)` に属する subdirectly irreducible 群は、K のどれかの元に埋め込める。
  - よって 𝒱₃ は、有限個の有限群 K について `ISP(K)` の形にならない。
  - これを一文書いておけば、「既知の定理の系ではないか」という査読者の疑問に先回りできる。
- 2026-09-05 公開の d'Elbée–Müller–Ramsey–Siniora, *Shirshov's amalgamated free product and
  generic nilpotent groups*, arXiv:2609.05789 も関係する。
  - p > c のとき、任意の（有限の）c-nilpotent 指数 p 群が、同じ class と指数の（有限の）
    UL-equivalent 群（下部中心列と上部中心列が逆順に一致する群）に埋め込める、と示している
    （pp.2–3、Theorem 4.1、Proposition 4.6）。これは Ivanov–Majcher (arXiv:2402.02143) の
    問題への解答である。
  - v8 の Lemma 4.6（1048–1086行、`G∗F₂` が UL-equivalent になる）と Proposition 4.13
    （e.c. モデル内の有界な envelope）は、この結果の範囲外にある c = p = 3 での類似物になっている。
  - 同じ著者群の論文の続編なので、査読で指摘される可能性が高い。

151行付近の修正案:

```tex
Burris and Werner proved that every universal Horn class generated by finitely many finite
structures has a model companion~\cite[\S8]{BurrisWerner1979} (see also
\cite[Theorem~1.1]{Burris1984}); this does not apply to $\mathcal V_3$, which contains finite
subdirectly irreducible groups of unbounded order.
```

151行本体は「we are not aware of a general criterion ...」程度に弱めるのが安全である。

### 1-5. 144行: Maier の結果は直接の帰属に

- Maier は Theorem 3.5（p.285）で、`c < p` のとき `K = N_c ∩ B^p` に ℵ₀-categorical な
  model companion が存在することを直接証明している。p.280 の要約にも「K and K′ do have model
  companions」とある。
- 「follows from Maier's amalgamation results」だと、著者らが導出したように読める。

```tex
For prime exponent $p$ and nilpotency class at most $c<p$, Maier proved that the theory has an
$\aleph_0$-categorical model companion~\cite[Theorem~3.5]{Maier1989}; see also
\cite[Corollary~4.42]{dElbeeMuellerRamseySiniora2025}.
```

## 2. 序論・abstract の文章で直したほうがよい点

| 行 | 指摘 | 修正の方向 |
|---|---|---|
| 103 | `Saracino-Wood` がハイフン | `Saracino--Wood` |
| 130 | 「model-companion problem」が未定義 | 「the question of whether a given theory of groups has a model companion」 |
| 131–132 | 3 つの例に出典がない。ES1971 は文献リストにあるのに、表示本文では引用されていない（`\if0` 内の 1502 行だけ） | ES1971 の Theorem 2.4（全アーベル群）を引用する。固定指数は Z/nZ 加群として ES1971 の coherent 環の結果からも従う |
| 136 | 原典は ES1971 の Theorem 7.17（p.291）。CK は p.609 の歴史注で 3.5.16 の出典を Eklof–Sabbagh (1971) としている | `\cite[Theorem~7.17]{EklofSabbagh1971}; see also \cite[Example~3.5.16]{ChangKeisler1990}` |
| 137 | 位置の指定がない。Takeuchi 2022 の p.80 は、この結果を最初に示したのは A. Tsuboi（私信、randomization による）と書いている | `\cite[Theorem~17]{Takeuchi2022}`。Tsuboi への言及は任意 |
| 138 | 「fixed derived length at least 2」は曖昧 | 「for every $n\ge2$, the theory of solvable groups of derived length at most $n$ has no model companion \cite[Theorem~1]{Saracino1974}」 |
| 139 | 位置の指定がない | `[Theorems~1 and~2]` |
| 140 | solvability は一階の条件ではない | 「a fixed bound on the derived length or on the nilpotency class」 |
| 142 | 「nilpotent classes」は nilpotency class と紛らわしい | 「some classes of nilpotent groups」 |
| 143 | 位置の指定がない | `[Theorem~3.9]`（ℵ₀-categorical であることも書ける） |
| 147 | 「some semisimple algebraic groups」が曖昧 | 「if $K$ is a model-complete field, then $G(K)$ for split semisimple $G$ over $K$ and $H(K)$ are model complete as pure groups」。HKTY Theorem 3.3、FK Theorem 3.6 を引く |
| 148 | 何に対する obstruction か書いていない | 「an obstruction to model completeness」 |
| 157 | 主語の「It」が指す $T_n$ は、可換な $T_2$ も含む | 「The family $(T_n)_{n>1}$」 |
| 165–166 | 「Thus」の根拠がない | 「Since every group of exponent 2 is abelian, ...」 |
| 180 | 「by the theory of vector spaces over $\mathbb F_2$」が曖昧 | 両辺とも成り立つ。$T_2$ の model companion は無限 $\mathbb F_2$ ベクトル空間の理論 |
| 181 | 指数 3 の有限性に出典がない。「the other side」が曖昧 | Burnside (1902) か LW1933 を引き、「the Main Theorem shows that the left-hand side also holds」 |
| 189 | $A$ の有限性が明示されていない | 「let $A\le M$ be finite」（$B$ が有限なので実害はない） |
| 191 | 「failure of amalgamation in the coproduct」は不正確。証拠は $A$ の二つのコピーを同一視した商にある | 表現を直す |
| 196–200 | display 数式の前後の空行（197・199行）で段落が切れ、PDF で「is injective.」が字下げされる | 空行を削除する |
| 206–209 | 「main theorem」の名前が二重になっている。785行の Theorem 3.3 の見出しは「Main theorem」だが、序論の Main Theorem は Corollary 3.4（826–828行） | 「Section 3 proves the bounded-witness theorem (Theorem 3.3) from Proposition A and deduces the Main Theorem (Corollary 3.4)」とし、Theorem 3.3 の見出しを変える |
| 211–215 | ①「We have also fully formalized」は、[AGENTS.md](../AGENTS.md) の役割分担（形式化の著者は石田のみ）と食い違う。②「soon」ではなく URL と版（Lean v4.34.0、Mathlib `5ed2965256430c3649e86755f9576b54eca72435`）を書く。③ git 履歴では 23 コミット中 14 に Claude が共著者として付いているが、AI 利用の開示（121–125行）は ChatGPT による証明の概略だけ | ①は「The first author has formalized ...」。③の扱いは著者の判断 |

確認して問題がなかった点:
- 121–125行の「GPT-5.6 Sol」は実在するモデル名である（OpenAI、2026 年 7 月公開）。
- 114–115行の MSC、03C60 と 20A15 は有効なコードである（下の §3）。
- 167行の LW1933 の引用は、p.155 と Satz 1 で確認した。class ≤ 3 で、それが達成される。
- 172行の Takeuchi 2022 の引用は、p.80 で確認した。固定指数と Burnside 問題の関連に触れている。

## 3. 参考文献リスト

### Crossref との照合

DOI をもつ 9 件と、追加候補の DOI をすべて Crossref の記録と照合した。
v8 の記載（著者、題、誌名、巻、号、頁、年）はすべて一致した。

| 文献 | Crossref の記録 | v8 との差 |
|---|---|---|
| dEMRS2025 | J. Algebra 662, 640–701, 2025 | なし |
| EF1972 | Ann. Math. Logic 4(2), 115–171, 1972 | 著者名の表記（1-1） |
| ES1971 | Ann. Math. Logic 2(3), 251–295, 1971 | なし |
| LW1933 | Abh. Math. Semin. Univ. Hambg. 9(1), 154–158, 1933 | 号の記載なし（任意） |
| Mai1989 | J. Algebra 127(2), 279–289, 1989 | なし |
| Sar1974 | Trans. AMS 197, 327–339, 1974 | なし |
| Sar1976 | Israel J. Math. 25(3–4), 241–248, 1976 | 号 3–4 の記載なし |
| SW1979 | J. Algebra 58(1), 189–207, 1979 | なし |
| Iva1992 | Bull. AMS 27(2), 257–260, 1992; DOI `10.1090/S0273-0979-1992-00305-1` | DOI の記載なし |

- 残りの文献:
  - CK1990（書籍）は、Google Books の in-volume 検索を再実行し、Example 3.5.16 が p.199 にあることを確認した。
  - Tak2022 は RIMS Kôkyûroku 2218, 79–84 で、PDF 6 頁と一致した。
- HKTY と FK は 2026-09-24 時点でも preprint である（arXiv に journal-ref がなく、Web でも出版を確認できない）。
  - 定理番号は HKTY v2（2025-03-02）と FK v2（2026-02-08）で確認した。
  - 文献欄に版を書くとよい。

### 形式の不統一

- 1561行の `CK90` は、1558行の方針「4 桁の年」に反する。`CK1990` にする。
- Ivanov に DOI がない。Sar1976 に号がない。Tak2022 に URL がない
  （<https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/2218-10.pdf>）。
- 投稿用の著者の所属・連絡先がない。

### 追加候補（書誌は Crossref または手元の原本で確認済み）

- P. C. Eklof, *Some model theory of abelian groups*, J. Symbolic Logic 37 (1972), no. 2, 335–342,
  doi:10.2307/2272976。
- P. S. Novikov and S. I. Adian, *Infinite periodic groups I, II, III*, Math. USSR-Izv. 2 (1968),
  209–236, 241–479, 665–685。DOI は `10.1070/IM1968v002n01ABEH000637`、
  `10.1070/IM1968v002n02ABEH000640`、`10.1070/IM1968v002n03ABEH000653`。
- S. I. Adian, *The Burnside Problem and Identities in Groups*, Ergebnisse der Mathematik und
  ihrer Grenzgebiete 95, Springer, 1979。
- W. Burnside, *On an unsettled question in the theory of discontinuous groups*,
  Quart. J. Pure Appl. Math. 33 (1902), 230–238。
- S. Burris and H. Werner, *Sheaf constructions and their elementary properties*,
  Trans. Amer. Math. Soc. 248 (1979), no. 2, 269–309, doi:10.1090/S0002-9947-1979-0522263-8。
- S. Burris, *Model companions for finitely generated universal Horn classes*,
  J. Symbolic Logic 49 (1984), no. 1, 68–74, doi:10.2307/2274092。
- C. d'Elbée, I. Müller, N. Ramsey and D. Siniora, *Shirshov's amalgamated free product and
  generic nilpotent groups*, arXiv:2609.05789 (2026)。
- （任意）A. Ivanov and K. Majcher, *Generic groups and the weak amalgamation property*,
  arXiv:2402.02143。

### MSC

- 03C60（Model-theoretic algebra）と 20A15（Applications of logic to group theory）は MSC2020 で有効である。
- model companion は 03C10（Quantifier elimination, model completeness, and related topics）に属する。
  Burris 1984 も 03C10 を付けている。
- 03C10 と 20F50（Periodic groups; locally finite groups）の追加を勧める。
- 変える場合は `formalization.yaml` の `msc2020` も合わせて直す。

## 4. 本文（§2–§5）

再計算して一致を確認したもの:
- この交換子規約（`[a,b]=aba^{-1}b^{-1}`、`a^b=b^{-1}ab`）での Fact 2.15 の各恒等式。
- Proposition 3.1（正規閉包の元は共役 3 個の積）。
- Lemma 3.2 の上界 `3(m+1)n`。
- Theorem 3.3 の証明の流れ。
- Proposition 4.4 のブロック計算。
- Lemma 4.6 の符号。`[[α,x],y] = −[α,[x,y]]` が、Jacobi 恒等式と三重ブラケットの交代性から出る。
- Lemma 4.7–4.10。
- Proposition 4.13 の上界 `(27n^2−3n+4)/2 ≤ 15n^2`。
- §5 の例。

軽微な指摘:
- 279–285行の Fact 2.3 に出典がない。298–312行の Fact 2.6 は証明付きなので、既知なら出典を付け、
  新しい結果なら Proposition にする。
- 261行の「Let $T$ and $T'$ be $L$-theories」と定義中の $T_0, T_1, T^*$ が対応していない。
  268行の「$T\equiv T'$」は「同じモデルをもつ」と書く。
- 346行の「$B'\subset M\models\theta_{B,A}(B',A)$」は記法が崩れている。
- 628行の Remark 2.28 の根拠が短すぎる。本来の根拠は、有限部分集合が生成する自由群の有向和と、
  その間の写像の単射性（retraction による）である。
- 811–812行の「generated by ... elements」は「at most」にする。
- 826–828行の Corollary 3.4 で、Fact 2.6 の仮定を明示する（普遍理論、有限言語、Fact 2.27 による局所有限性）。
- 834行で、G を導入する前に「presentation of $G$」と書いている。
- 1065行（Lemma 4.6 の Case 1）の符号の根拠を一行加える。
- 1361行の $H$ が定義されていない。「in any $H\in\mathcal V_3$ containing $G$」とする。
- 1418行と 1441行で、$F_3$ の変数名（$s,x,y$ と $s,y,z$）が違う。
- `eqnarray*`（969、975、981、987、1005、1019、1137、1151、1189、1239、1252 行）は `align*` にする。

## 5. 一致を確認した引用

| 引用 | 原典の所在 | 判定 |
|---|---|---|
| CK Example 3.5.16 | p.199（Google Books の in-volume 検索、2026-09-24 に再実行） | 一致。p.609 の注で ES1971 を出典にしている |
| ES1971 | Theorem 2.4 p.256、Theorem 7.17 p.291 | 一致 |
| Sar1974 | Theorem 1 p.327 | 一致（表現の精密化を推奨） |
| Sar1976 | Theorem 1 p.241、Theorem 2 p.242 | 一致 |
| SW1979 | Theorem 3.9 p.198（`2 ≤ m < ∞`、定義は p.189） | 一致 |
| Mai1989 | Theorem 3.5 p.285、要約 p.280 | 一致（直接の帰属に直す） |
| dEMRS2025 | arXiv v3、および同日追加入手した出版社配布AMのCorollary 4.42、pp.33–34（Lazard対応の条件は奇素数 `p > c`） | 一致。AMの番号も確認済み。最終組版版の番号は未確認。 |
| HKTY2023 | arXiv v2 の Theorem 3.3 | 一致 |
| FK2025 | arXiv v2 の Theorem 3.6 | 一致 |
| LW1933 | p.155（交換子規約 (5)、(6)、class ≤ 3）、p.157 の Satz 1 | 一致 |
| Tak2022 | p.80（Burnside との関連、Tsuboi への言及）、p.83 の Theorem 17 | 一致 |
| Iva1992 | Theorem A、p.258 | 主張は含む。階数と帰属を直す |

## 6. 未確認・残課題

- dEMRS2025 の最終組版版（Version of Record）での Corollary 4.42 という番号。同日追加入手した
  出版社配布AMのpp.33–34では番号・内容を確認したが、最終組版版との対応は未確認。
  [AMの照合記録](/home/ywr/t3-model-companion/notes/audit-artifacts/2026-09-24/v8-reference-review/demrs-accepted-manuscript-review.md)。
- F. Leinen による、局所有限な群のクラスにおける e.c. 群の一連の研究（Comm. Algebra 13 (1985)、
  サーベイ *Existentially closed groups in specific classes*, 1995, pp.285–326）。
  本文を入手できず、v8 との重なりの有無を確認していない。
- 新規性の文献調査は網羅的ではない。

## 7. 前回レビューとの関係

- 維持する結論:
  - 133行の誤帰属、183行の階数条件。
  - Saracino・SW・Maier・ES・Tak・LW の原典との一致。
  - CK の例番号と頁。
- 更新・追加した結論:
  - 183行の帰属（Novikov–Adian／Adian）。
  - 201行の論理の向き。
  - 151行と Burris–Werner、arXiv:2609.05789。
  - 144行を直接の帰属にすること。
  - EF の著者名の表記（Fisher）。
  - 196–200行の段落切れ、206–209行と 785行の名前の衝突、211–215行の役割分担と開示。

## 証拠

- 新しく保存した外部資料（arXiv:2609.05789v1 の PDF と抽出テキスト、Crossref と arXiv API の生の応答、
  MSC2020、Burris 1984 の 3 頁の描画）は、別途保管した文献資料
  `references/` にある。
  MANIFEST の section 27 に来歴と SHA-256 を記録した。
- 既存の証拠（出版版 PDF とページ画像）は、MANIFEST の sections 21–26 の登録どおり、その場で参照した。
- 詳細: [証拠の保存先](audit-artifacts/2026-09-24/v8-paper-review/README.md)、
  [照合一覧](audit-artifacts/2026-09-24/v8-paper-review/source-inventory.json)。

> 公開履歴の整理に伴い、非公開の作業場所・内部識別子を省略した。数学的記述と当時の検証結果は保持しており、ここに記す検証は当時の対象に限る。
