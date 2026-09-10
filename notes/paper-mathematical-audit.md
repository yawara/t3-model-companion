# T3 論文 v4 の数学的検証

検証日: 2026-09-09。

**判定: 主定理とその系、および本文の明示的な上界を支える論証は成立すると判断する。今回確認した定理に、主張の変更・追加仮定・別証明を必要とする欠陥は見つからなかった。** 一方、いくつかの「明らか」「同様」の部分には、形式化に先立って明記すべき省略がある。その数学的内容を以下に補う。

この判定は、AI agent が TeX 本文の定義・量化・証明を読み、依存順に再導出した結果である。主要な群論的外部入力は Levi–van der Waerden の原論文のページ画像で確認した。原稿の読解と Lean の機械検証は別の検査であり、この読解時点の記録は v4 全体の Lean 証明の完成を主張しない。

## 一次資料

- 検査対象: [T3_modelcompanion_v4.tex](../T3_modelcompanion_v4.tex)、1309 行。
- SHA256: `79745dfa1660a827c51ec3c6b2006ee9d6243cb4702f97a75e5b55357b89f50b`。本文は変更していない。

以下の原典ページを画像で読んだ。

| 原典 | 確認箇所 | 支持する内容 |
| --- | --- | --- |
| Levi–van der Waerden (1933), pp.154–155 | (4)–(6) | 共役元との可換性、交換子の反転・巡回恒等式、derived subgroup の可換性、三重交換子の中心性 |
| 同 pp.156–157 | (8), (9), Satz 1 | 正規形、座標積、指数 3 の群構成、一意性、位数 `3^(r+binom(r,2)+binom(r,3))` |
| Hall (1958), p.765 | (2.1), (2.6) | 基本恒等式と collecting process の再記述。正規形の一意性は上記原論文から取る |
| Burris–Lawrence (1979), p.162 | Claims 4–6 | 共役圧縮の比較。v4 の幅 3 は、同論文の幅 5 を引用するだけでなく v4 本文の式から直接検証した |

書誌情報は原稿末尾の参考文献一覧に対応する。上表のページ番号は原典の印刷ページである。

モデル理論の標準入力「inductive 理論の e.c. class の一階公理化可能性と model companion の存在の同値」は、[Kruckman, Math 509 notes, Theorem 6.38](https://akruckman.faculty.wesleyan.edu/files/2025/12/Lecture-Notes.pdf) の本文でも仮定と結論を確認した。以下の bounded-witness criterion の検証は、TeX の証明を直接追ったものである。

## 1. 基本恒等式と外積による Lie algebra

TeX 146 の交換子は `[a,b]=aba⁻¹b⁻¹`、共役は `a^g=g⁻¹ag`。この規約を保ったまま 355–369 の恒等式を確認した。Levi–van der Waerden p.155 の交換子規約も前者と一致する。Hall の逆順の規約をそのまま混ぜない。

TeX 361 の「Z₂(G) は可換とは限らない」も正しい。例えば非可換な B(2,3) は class 2 なので Z₂(G)=G である。有限指数 3 群が class 3 になり得ることは B(3,3) の非零の三重座標で分かる。

TeX 289–305 の truncated exterior algebra の bracket では、交代性は degree 1 の wedge と degree (1,2)/(2,1) の符号相殺から従う。Jacobi の非零となり得る場合は三つの入力がすべて degree 1 の場合だけで、

\[
u\wedge v\wedge w+v\wedge w\wedge u+w\wedge u\wedge v
=3u\wedge v\wedge w=0.
\]

したがって標数 3 を正しく使っており、3 で割る議論も Lazard correspondence の不適切な使用もない。正次数 graded Lie algebra が degree 1 で生成されることと `[L_i,L_1]=L_{i+1}` の同値は、Jacobi により任意の Lie word を左結合形の和に直すことで従う（281–287）。

TeX 391–418 の associated graded の bracket は、代表元を γᵢ₊₁、γⱼ₊₁ の元だけ変えたときの誤差が γᵢ₊ⱼ₊₁ に入るため well-defined。加法性は交換子の積公式を次の次数で割って得る。正規形の次数別の基底から 550–601 の σᵢ は全単射である。順序の異なる添字の bracket は交換子の交代性・巡回性で処理できる。

無限 rank の正規形（535–547）は、各群の語が有限個の生成元しか使わないことと、有限自由因子への retraction から従う。外積・tensor・直和も代数的な有限支持のものなので、無限次元で余計な完備化は不要。

## 2. 一般の quotient と非斉次な関係式

TeX 623–641 の canonical quotient formula は正しい。γᵢ₊₁(G)≤γᵢ(G) を使う modular law により、誘導全射の kernel は

\[
\gamma_{i+1}(G)(N\cap\gamma_i(G))/\gamma_{i+1}(G)
\]

であり、これは定義どおり grᵢᴳ(N) である。

TeX 753–799 の基底 lift の生成性も有限生成を仮定せず成立する。H を lift の生成部分群とすれば `G=Hγ₂(G)`。γ₂ の可換性より

\[
\gamma_2(G)\le H[H,\gamma_2(G)]\le H\gamma_3(G).
\]

γ₃ の中心性から `[H,γ₂(G)]≤[H,H]≤H`、従って γ₂(G)≤H、G=H。abelianization 上では基底を基底へ送るので同型となり、kernel は derived subgroup に含まれる。

normal closure の補題（802–840）では、K≤γ₂(G) が degree 2 と degree 3 の直和に分裂すると仮定する必要はない。`P=[K,G]≤γ₃(G)≤Z(G)` とすれば

\[
L=KP,\qquad L\cap\gamma_3(G)=(K\cap\gamma_3(G))P.
\]

後者は、kp∈γ₃(G) と p∈γ₃(G) から k∈γ₃(G) とするだけである。これが本文の graded image の式をそのまま与える。

この点は、例えば B(5,3) 内の `[x₁,x₂][x₃,x₄,x₅]⁻¹` のように次数を混ぜた関係式でも破綻しない。degree 2 の image を消したことから degree 3 の成分まで個別に消したと誤って推論していない。

## 3. coproduct の分解、自然性、strict inclusion

TeX 843–929 の一般 coproduct 命題を、非斉次な K₀,K₁ を許したまま確認した。

F=F₀*F₁、K=K₀K₁ とすると、degree 2 の pure block は独立である。より直接には、`k₀k₁∈γ₃(F)` に対して二つの因子への retraction を適用すれば `kᵢ∈γ₃(Fᵢ)` となる。従って 911 行で使う

\[
K\cap\gamma_3(F)
=(K_0\cap\gamma_3(F_0))(K_1\cap\gamma_3(F_1))
\]

が成立し、`gr₃(K)=S₀⊕S₁` が得られる。Kᵢ の normality から `Rᵢ∧Vᵢ⊆Sᵢ` も従う。その結果、normal closure の degree 3 image は

\[
S_0+(R_0\wedge V_1)+(V_0\wedge R_1)+S_1
\]

となる。各項は別の block に入るので quotient を block ごとに取れ、体 F₃ 上の tensor の exactness により本文の η₁,η₂,η₃ の同型を得る。

**符号の説明を一文足す必要がある。** 856 行で定義する η₃ の `V₀⊗gr₂(G₁)` 成分は `[u,q]` なので、通常の外積表示では `−u∧q` である。従って通常の外積の直和同型に、その block 上の `−id` を合成したものが本文の η₃ になる。これは命題の誤りではなく、同一視の説明の省略である。後続の 979、984、997、999、1068 行はこの符号で整合している。

ηᵢ は最後には canonical factor maps と bracket だけで定義されるため、基底・lift の選択に依存せず自然である。この自然性を使うと、strict inclusion の induced map は各 direct-sum/tensor block 上で単射となる。体上の tensor は単射を保つので、有限性の仮定なしに strict coproduct 補題（946–958）が従う。gr(f) の単射性から f の単射性への移行は、非自明 kernel 元の最後の非零 filtration degree を取る 478–484 行の議論で正しい。

## 4. F₂ で十分であること

TeX 962–1001 の **G≠1** は不可欠であり、明記されている。もし `G/γ₂(G)=0` なら `G=γ₂(G)=γ₃(G)=γ₄(G)=1` なので、非自明な G には必ず非零の abelianization 成分がある。これは無限群にも通る。

V=gr₁(G)、W=⟨x,y⟩ とする。degree 1 の元 α+β が非零なら、

- α≠0 のとき `[[α,x],y]` の `V⊗Λ²W` 成分は `−α⊗(x∧y)≠0`。
- α=0、β≠0 のとき、`0≠ḡ∈V` と β に独立な w̄∈W を選べば `[[β,ḡ],w̄]=ḡ⊗(β∧w̄)≠0`。

これにより Z₂(H)=γ₂(H)。degree 2 では `α₂+α₁⊗x+α₁′⊗y+β₂` の非零成分を、順に x、y または x、非零の ḡ と bracket して検出できる。異なる block の成分は相殺しない。従って Z(H)=γ₃(H)。G→H の strictness は coproduct 分解または因子への retraction から従う。

G=1 の場合には H=F₂ で `Z(H)≠γ₃(H)` となるので、この仮定を形式化時に落としてはいけない。

## 5. 同時 root 付加と次元による上界

### commutator roots（1010–1108）

rᵢ=gᵢ⁻¹[xᵢ,yᵢ] は derived subgroup に入り、`h↦[rᵢ,h]` は中心への準同型である。L∩G の元を `a=∏rᵢ^{mᵢ}[rᵢ,hᵢ]` と書いたとき、自由因子の degree 2 成分 `∑mᵢ(xᵢ∧yᵢ)` は 0 なので全 mᵢ=0。

`gr₁(hᵢ)=sᵢ+tᵢ` と分ける。degree 3 の `gr₁(G)⊗Λ²V₂ₙ` 成分は `−∑sᵢ⊗(xᵢ∧yᵢ)`。独立な wedge に対する双対座標を適用すれば全 sᵢ=0 となり、残る G 側の成分も `−∑[gr₂(gᵢ),sᵢ]=0`。従って a=1。**tᵢ=0 を導く必要はない。** 別の混合 block にある `−∑gr₂(gᵢ)⊗tᵢ` は、a∈G によってその成分が 0 である。因子の strictness は前節から得られるので、a の次数を G 内で扱うことも正当である。

`(C∩γ₂(G))/γ₂(C)` は C/γ₂(C) の部分空間なので、その基底の長さは d(C) 以下。各基底元につき二つの root を付加すれば、追加生成元数は **2d(C)** 以下になる。quotient の関係式はすべて degree 2 以上なので abelianization は変わらず、本文の新座標を消す議論で derived strictness が従う。

### triple roots（1110–1175）

gᵢ と `[xᵢ,yᵢ,zᵢ]` はともに中心的なので、normal closure は生成部分群に等しい。`a∈G∩L` を自由因子に射影して、独立な `xᵢ∧yᵢ∧zᵢ` の係数を比べれば全指数が 0 となる。1127 行の推論にはこの独立性を明記する。

derived strictness を仮定すると

\[
(C\cap\gamma_3(G))/\gamma_3(C)
\le\gamma_2(C)/\gamma_3(C).
\]

n 生成自由群からの全射は degree 2 でも全射なので、右辺の次元は binom(n,2) 以下。従って追加生成元数は **3binom(n,2)** 以下。

1150–1174 行の quotient/intersection 計算も成立する。特に degree 3 の計算では L⊆γ₃(C×F₃ₘ) と誤って仮定せず、`(γ₃(C)×γ₃(F₃ₘ))L` を残している。選んだ gᵢ の余剰成分を新しい triple roots 側へ移すことで、両 strictness が成立する。

root family の空・重複・自明元の場合にも問題はない。1177–1182 行の 4 生成元で 4 つの独立 triple coordinates を使う remark も、Λ³(F₃⁴) の四つの基底 wedge の独立性で成立する。

## 6. e.c. 転送と 15n²

e.c. モデル M は非自明である。M×C₃ で `∃x(x≠1)` が真なので、e.c. 性で M 内でも真になる。これを明記すれば、1185–1207 行で F₂ の補題を M に適用できる。root equations と非零交換子の witness は存在式なので M へ戻せ、本文の中心列一致と単一交換子表示が従う。

1212–1251 行では C≠1 なら n≥1。二段階の strictification と F₂ の追加により

\[
d(D_3)\le 3n+3\binom{3n}{2}+2
=3n+\frac{9n(3n-1)}2+2\le15n^2.
\]

最後の差は `(3n²+3n−4)/2≥1`。C=1、特に n=0 の場合は **D=1** を選ぶ。この場合に F₂ を追加してはいけない。

D₃ は有限生成の指数 3 群なので有限。その乗法表・逆元・相異性・C の固定を有限個の量化子なし条件で指定し、存在式として M に戻すことで `D≅_C D₃` を得る。内部的な中心列一致はこの同型で保存される。

最後の strictness は

\[
D\cap\gamma_2(M)\subseteq D\cap Z_2(M)\subseteq Z_2(D)=\gamma_2(D),
\]
\[
D\cap\gamma_3(M)\subseteq D\cap Z(M)\subseteq Z(D)=\gamma_3(D)
\]

と逆包含の自然性から従う。ここには M 自身の e.c. 中心列等式さえ不要で、証明の循環はない。よって Proposition A では **f₀(n)=15n²** を選べる。

## 7. 共役幅、support、主定理の具体的な関数

TeX 653–665 の幅 3 は正しい。`t=[a,g,g′]` とおくと

\[
[a,gg']=[a,g][a,g']t,\qquad [a,[g,g']]=t^{-1}.
\]

中心性により `[a,gg′[g,g′]]=[a,g][a,g′]`。従って本文の Eₐ は部分群で、全共役を含み normal closure に含まれるから等しい。指数 k=1,2,0 の三場合は、それぞれ `a^g`、`a·a^g`、`a·a·a^g` と書ける。

668–693 行では Q=H/γ₃(H) が class 2 である。B の m 個の生成元 bⱼ を固定すると、cross commutators は双加法性により `[u,bⱼ]` の形へ分解できる。同じ j の項は `[u,bⱼ][u′,bⱼ]=[uu′,bⱼ]` で一つにまとめられる。従って共役元一つにつき G の元は高々 m+1 個でよく、γ₃(H) の誤差は共役作用を変えない。

有限族へ戻す際は、各 δᵢ の共役数を kᵢ≤3 と書き、

\[
\sum_{i<r}k_i(m+1)\le3r(m+1)\le3n(m+1)
\]

とすればよい。692 行の単一の k の記帳は、この和または `max_i k_i` にするのが明瞭。これは定数の誤りではない。Δ=∅ なら h=1、C=1 を直接選べる。

主定理（704–739）は、A の生成元について二つの因子写像を同一視した quotient が pushout になることから始まる。両因子写像が単射なら amalgam なので、非 amalgamation は非自明 kernel 元を与える。support と A と必要なら g を追加した C の生成元数は `3(m+1)n+n+1` 以下。

有限指数 3 群は有限 3 群なので `d(A)≤log₃|A|`。A≤B と正規形の位数公式により `n≤t(m)`。Proposition A を `N=(3m+4)t(m)+1` に直接適用すればよく、f₀ の単調性を仮定する必要はない。

strict coproduct の単射性により certificate を D*B 内に戻すと、非自明な g がその pushout で消えるため、D と B も A 上 amalgamate できない。B 側で kernel 元が見つかる場合も、C に g を追加する必要がないだけで同じ上界が使える。A=1 または m=0 では非 amalgamation の前提自体が成立しない。

従って、本文の主定理には具体的に

\[
\boxed{f(m)=15\bigl((3m+4)(m+\binom m2+\binom m3)+1\bigr)^2}
\]

を選べる。

## 8. 一般モデル理論の criterion

TeX 175–263 の範囲も仮定を保持して検査した。Π₂ は inductive theory であり、e.c. モデルへの拡大と e.c. class の一階公理化による model companion の特徴づけが適用できる。

局所有限性からの一様位数 bound（209–212）は次の compactness で補える。有限言語なので「指定 tuple を含み、定数とすべての関数に閉じた高々 k 元の集合が存在する」を一階式 χₖ で表せる。これは生成部分構造の位数≤k と同値。すべての ¬χₖ を T に加えた理論が不充足なので、compactness により一様な k がある。

有限言語・一様位数 bound から有限生成部分構造の指定 tuple 付き同型型は有限個。量化子なし式の真偽はその型で決まるので、有限図式を用いる 185–191、231 行の議論も正しい。

criterion の必要方向（233–243）では、否定された extension formula を model companion 上で存在式へ書き換え、その witness と A が生成する C を取る。C 自身が T のモデルである必要はない。仮想 amalgam N₀⊨T に C の量化子なし情報を移し、N₀ を model companion のモデルへ埋めれば、B の存在とその否定が両立して矛盾する。

十分方向（245–262）では K(A,B) が有限である。257 行の “clearly” には、**K のコピーがない ⇒ 仮定 (2) の対偶から M と B が amalgamate できる ⇒ e.c. 性で B のコピーを M に戻す**、という一段を補う。

逆に extension scheme のモデル M に対して、M⊆N の存在式の witness が生成する有限 B と、パラメータが生成する有限 A を取る。禁止 C のコピーが M にあれば N が B と C の amalgam になるので、K の定義に反する。従って scheme を適用して B のコピーを M に得る。この証明は bounded witness を e.c. モデル上だけ仮定している点と整合する。

T₃ は universal、従って Π₂ で、正規形定理により局所有限。この criterion を上記の f に適用すれば、743–745 行の系「T₃ は model companion をもつ」が従う。

## 9. 独立な正確計算と残る記述上の整備

原論文 p.156 の座標積 (9) を独立した [Python 検査](audit-artifacts/2026-09-09/check_paper_identities.py) に写し、F₃ 上の多項式として計算した。rank 4 の 14 座標を持つ任意の 4 元を、56 個の独立な不定元で表現している。

群の結合律・単位元・指数 3 と、四重交換子消滅、巡回恒等式、二つの積公式、共役圧縮など、**16 件 / 各 14 座標**の差が厳密に 0 となった。誤った符号の積公式二つと「三重交換子は常に 1」は検出されることも確認した。浮動小数点・乱数・有限個のサンプルへの代入は用いていない。[結果 JSON](audit-artifacts/2026-09-09/paper-identities.json) を保存した。

この計算は基本恒等式の補助検査であり、coproduct 命題や model companion の証明全体を機械検証したものではない。主たる判定根拠は上記の数学的な再導出である。

形式化前の補筆箇所は、以下に集約できる。いずれも新しい仮定を導入せず埋められる。

| TeX 行 | 補足する内容 |
| --- | --- |
| 257 | bounded-witness 仮定の対偶と e.c. 性の二段階 |
| 535–547 | 無限 rank での有限支持・自由因子 retraction |
| 692 | singleton の k を有限族の Σkᵢ として記帳 |
| 856–928 | η₃ の (1,2) block の負号、同型の自然性、非斉次関係式の交差計算 |
| 982,999 | G≠1 から gr₁(G)≠0 |
| 1056,1070,1127 | 因子の strictness と distinct wedge の線形独立性 |
| 1203–1207 | e.c. M の非自明性、および “similar argument” の witness |
| 1223,1250–1251 | C=1 の処理、有限図式の相異性、内部中心列一致から strictness |

abstract の歴史的帰属・Takeuchi の予想の出典、Introduction/Applications/Further questions の執筆 placeholder、全参考文献の書誌的照合は、この数学的な主定理検証とは別である。Saracino–Wood、Maier の原論文全文は今回取得・精査していないため、その帰属まで原典確認済みとはしない。引用される範囲の概要は [d'Elbée et al. の刊行論文の Introduction](https://www.sciencedirect.com/science/article/abs/pii/S0021869324004757) と整合するが、それを原論文全文の検証の代用にはしていない。
