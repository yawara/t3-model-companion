# 有限 A-group が生成する variety と有限 retract による方法

2026-09-22。第6節 Question 6.1 の追加検討である。
以下の結論は通常の群言語 `{1, ·, ⁻¹}` に関するもので、文献の定理と本ノートの
数学的証明に基づく。新しい議論は Lean では形式化していない。
局所有限な群 variety 全体についての Question 6.1 を解決するものではない。

## 1. 文献から得られる肯定範囲

有限群 `H` のすべての Sylow 部分群が可換なとき、ここでは `H` を **A-group** と呼ぶ。
`V(H)=HSP(H)` は `H` が生成する群 variety、`ISP(K)` は `K` の任意の直積の部分群の
同型類全体を表す。

次が一次文献の正確な入力である。

- Olshanskii, *Varieties of finitely approximable groups*, Theorem 1, p.867:
  群 variety `V` の**すべての群**が残余有限であることと、`V` が有限 A-group により
  生成されることは同値である。
- 同 Theorem 2, p.867: `V` のすべての群が残余有限なら、ある有限 `K∈V` が存在し、
  `V` の各群は `K` の直積に埋め込まれる。
- Burris, *Model companions for finitely generated universal Horn classes*,
  Theorem 1.1, p.69: 有限個の有限代数が生成する universal Horn class は
  model companion を持つ。この場合の生成は `ISP` である。

出典は [Olshanskii の原論文](https://www.mathnet.ru/eng/im2186)
（[英訳全文](https://www.mathnet.ru/php/getFT.phtml?jrnid=im&option_lang=eng&paperid=2186&what=fullteng)）と
[Burris の著者公開本文](https://www.math.uwaterloo.ca/~snburris/htdocs/MYWORKS/PAPERS/Model%20Companions.pdf)
である。Olshanskii の旧用語 “finitely approximable” は残余有限の意味である。

**帰結。有限 A-group `H` が生成する `V(H)` は model companion を持つ。**

実際、最初の二定理から有限 `K∈V(H)` があり `V(H)⊆ISP(K)` となる。
逆包含は `K∈V(H)` と variety の部分群・直積閉性から従う。
従って `V(H)=ISP(K)` で、Burris の定理を適用できる。
ここでは `K=H` とは仮定しない。有限 `H` から `HSP(H)=ISP(H)` が自動的に
従うという議論ではない。

群 variety は直積により joint embedding property を持つ。
群言語は有限なので、さらに Burris Theorem 1.2, p.69 により、この model companion は
complete で、`H≠1` なら `ω`-categorical である。`H=1` では自明群の完全理論となる。
この記述は通常の群言語についてのものである。
quantifier elimination や model completion はここでは主張しない。

これは非冪零な例 `V(S₃)` を含み、さらに非可解単純群 `A₅` が生成する `V(A₅)` も含む。
`S₃` の Sylow 部分群は `C₂,C₃`、`A₅` では `C₂²,C₃,C₅` であり、すべて可換である。
すべての有限単純群にこの議論を適用できる、という主張ではない。

## 2. 局所有限性と `ISP` 条件の差

任意の有限群 `H` に対し `V(H)` は局所有限である。
相対自由群 `F_{V(H)}(n)` の元を `Hⁿ→H` という語の関数として評価すれば、

\[
 F_{V(H)}(n)\hookrightarrow H^{H^n},\qquad
 |F_{V(H)}(n)|\le |H|^{|H|^n}.
\]

評価写像の単射性は、`H` で成立する恒等式が `V(H)` の恒等式そのものであることから従う。
任意の `n` 生成群はこの有限群の商なので有限となる。

一方、`ISP(K)` への所属は、群全体から有限 `K` への準同型で各非自明元を分離できることを
要求する。有限部分群からの準同型が群全体へ延長できるとは限らない。
したがって局所有限性だけからこの条件は得られない。
Olshanskii Lemma 1, pp.868–869 は、すべての群が残余有限な variety に含まれる冪零群は
すべて可換であることも述べる。
指数3の variety は非可換冪零群を含み、本論文の model companion の肯定例である。
従って本節の条件は必要条件ではない。

## 3. 有限 centerless monolithic 群の場合の直接構成

以下では、有限非自明群 `K` に対して

\[
 Z(K)=1,\qquad K\text{ は monolithic},\qquad V=ISP(K)
 \text{ は群 variety}
\tag{*}
\]

を仮定する。monolithic とは、すべての非自明正規部分群に含まれる非自明正規部分群
`N`、すなわち monolith が存在することである。
`k=|K|`、`d=d(K)` を `K` の最小生成元数とする。
この節の構成は前節の model companion の存在を再引用せずに進む。

### 3.1. `Kʳ` は absolute retract

`E=Kʳ`、`r≥1` とする。任意の埋め込み `E≤D∈V` は retraction `D→E` を持つ。
これは「absolute retract」の意味であり、任意の部分群からの準同型を延長する
categorical injectivity とは区別する。

各因子の monolith から `1≠nᵢ∈Nᵢ` を選ぶ。
`D∈ISP(K)` なので、ある準同型 `φᵢ:D→K` が `nᵢ` を殺さない。
第 `i` 因子 `Kᵢ` 上での核が非自明なら、それは `Nᵢ` を含み `nᵢ` を殺すから矛盾する。
従って `φᵢ|Kᵢ` は単射であり、`K` が有限なので自己同型 `αᵢ` である。
他の因子の像は `φᵢ(Kᵢ)=K` と可換なので、`Z(K)=1` により自明である。
よって `ψᵢ=αᵢ⁻¹φᵢ` の `E` への制限は第 `i` 射影となる。
積写像 `(ψ₁,…,ψᵣ):D→Kʳ` が求める retraction である。

特に `E` は amalgamation base である。
`E≤B,C∈V` に対して retraction `r_B:B→E`, `r_C:C→E` を選び、

\[
 b\longmapsto (b,r_B(b)),\qquad
 c\longmapsto (r_C(c),c)
\]

で `B,C` を `B×C` に埋め込む。ここでは `E` の各側への包含を省略して書いた。
両写像は `E` 上で `e↦(e,e)` に一致し、各々の対応する射影により単射である。

### 3.2. e.c. 群の中での一様な有限 envelope

`M∈V` が existentially closed、`A≤M` が `n` 生成とする。
`X=Hom(M,K)` と置き、制限の集合

\[
 R=\{\varphi|_A:\varphi\in X\},\qquad r=|R|
\]

を考える。制限は `A` の `n` 個の生成元上の値で決まるので `1≤r≤kⁿ` である。
`M∈ISP(K)` だから、評価写像 `M→Kˣ` と `A→Kᴿ` は単射である。
制限による全射 `X→R` から、前合成による単射 `Kᴿ→Kˣ` が得られる。
これらは `A` 上で一致する。従って `M` と `E=Kᴿ` は `A` 上で `Kˣ` に amalgam する。

有限群 `E` の全乗法表と相異なる元どうしの不等式を、`A` の元をパラメータとして書く。
これは有限 existential diagram であり、上の拡大で実現する。
`M` の e.c. 性により `M` 自身で実現し、`A` を固定する埋め込み `E→M` を得る。
その像を改めて `E` と書けば

\[
 A\le E\le M,\qquad E\cong K^r,\qquad
 |E|\le k^{k^n},\qquad d(E)\le d\,k^n.
\tag{1}
\]

最後の評価には、各因子の `d` 個の生成元を合わせた生成集合を用いる。
非可換直積の最小生成元数についての等式は仮定していない。

### 3.3. 非 amalgamation の witness の一様な rank bound

`M` と `B∈V` が `A` 上で amalgam しないとする。`B` の有限性は必要ない。
上の `E` について、`E` と `B` も `A` 上で amalgam しない。

実際、もし `E,B` の amalgam `H∈V` があれば、`E` は `M` と `H` の両方の
retract である。3.1 の直積構成で `M,H` を `E` 上で amalgam し、そこへ `B` を
合成すれば `M,B` の `A` 上の amalgam を得て矛盾する。
従って (1) は、e.c. モデルの中の非 amalgamation witness に対する

\[
 b_K(n)=d(K)\,|K|^n
\tag{2}
\]

という rank bound を与える。これは相手 `B` の生成元数に依存しない。
e.c. 群の**内部に** `E` を実現する手順が、この結論で必要な点である。

### 3.4. 通常の群言語での model companion の直接証明

有限群 `F` の全乗法表と全ての不等式を表す量化子なし有限 diagram を `Δ_F` と書く。
以下の二種類の一階公理を、`V` の恒等式に加える。

1. 各有限 `A∈V` と `n=d(A)` について、`A` の各埋め込みは、ある
   `1≤r≤kⁿ` と埋め込み `j:A→Kʳ` に沿って `Kʳ` の埋め込みへ延長できる。
   式は `∀ā (Δ_A(ā) → ⋁_{r,j} ∃ȳ Δ_{Kʳ,j}(ā,ȳ))` である。
   `r` と `j` の選択肢は有限なので、これは一階文である。
2. 各 `r≥1` と有限拡大 `Kʳ≤B∈V` について、`Kʳ` の各埋め込みは
   `B` の埋め込みへ延長できる。
   式は `∀ē (Δ_{Kʳ}(ē) → ∃z̄ Δ_{B,Kʳ}(ē,z̄))` である。

e.c. 群は第一の公理を 3.2 により満たす。
第二の公理は `Kʳ` が amalgamation base であることと e.c. 性から従う。
逆に二種類の公理を満たす `M` と拡大 `M≤D∈V` を取る。
`D` で実現する有限 existential formula のパラメータが生成する部分群を `A` とする。
局所有限性により `A` は有限である。
第一の公理により `A≤E≤M`, `E≅Kʳ` を取り、`E` と選んだ witness tuple が `D` 内で
生成する有限群を `B` とする。第二の公理は `B` を `E` 上で `M` に埋め込む。
この埋め込みは量化子なし式を保存するので、元の existential formula は `M` でも実現する。
従って `M` は e.c. である。

これで e.c. モデルの類が公理化された。
普遍理論の各モデルが e.c. 拡大を持つ標準的な鎖構成と Robinson の model-completeness
criterion を用いれば、この公理系は `V` の model companion となる。
この節では有限群の埋め込みを通常の群言語の diagram で記述しており、追加の述語や
定数による言語拡大を必要としない。

## 4. `S₃` と `A₅` に対する仮定の確認

前節の直接構成で `K` を指定するには `V(K)=ISP(K)` の確認が必要である。
Olshanskii Theorem 3, p.868 によれば、有限群 `K` について
`qvar(K)=var(K)` となる必要十分条件は、`K` が A-group であり、そのすべての
monolithic section（部分群の商）が `K` に埋め込まれることである。
有限 `K` に対して `qvar(K)=ISP(K)` なので、この定理が利用できる。

`S₃` の sections は `1,C₂,C₃,S₃` であり、全て `S₃` に埋め込まれる。
また `S₃` は centerless、monolith は `C₃` である。
従って `V(S₃)=ISP(S₃)` で、(1)–(2) を `k=6,d=2` で適用できる。

`A₅` の部分群は同型を除き

\[
 1,\ C_2,\ C_3,\ C_5,\ C_2^2,\ S_3,\ D_{10},\ A_4,\ A_5
\]

である。このリストは、例えば Naughton–Pfeiffer の
[table of marks の論文、Figure 4](https://maths.nuigalway.ie/research/Preprints/2011/IRL-GLWY-2011-004.pdf)
で確認できる。ここで `D₁₀` は位数10の dihedral group である。
`C₂²` の商はこのリストに入り、`S₃,D₁₀` の非自明な真の商は `C₂`、
`A₄` のそれは `C₃`、単純群 `A₅` には非自明な真の商がない。
従って全 sections が `A₅` に埋め込まれる。
`A₅` は centerless かつ単純、従って monolithic なので、`V(A₅)=ISP(A₅)` となり
前節を適用できる。

## 5. categorical injectivity と amalgamation property との区別

### 5.1. injectivity は必要ない

`V(S₃)` の中で、位数3の元を含む categorical injective group は存在しない。
実際、`A=C₃×C₃≤B=S₃×S₃` とし、二つの `C₃` の生成元を同じ位数3の元 `a∈J`
へ送る準同型 `A→J` を考える。
これが `B→J` に延長できたとすると、第1因子の transposition の像は、第一の生成元の像
`a` を反転し、第二の生成元の像 `a` を中心化する。
従って `a=a⁻¹` となり、位数3に矛盾する。

これに対し `S₃ʳ` は 3.1 で示した absolute retract である。
本構成が必要とするのは後者であり、有限 categorical injectives の十分な存在ではない。

### 5.2. `V(S₃)` は amalgamation property を持たない

`A=(𝔽₃²,+)` に対し、列ベクトルへの作用を

\[
 d=\begin{pmatrix}-1&0\\0&1\end{pmatrix},\qquad
 e=\begin{pmatrix}-1&2\\0&1\end{pmatrix}
\]

で定める。ともに位数2であり、\(P=\begin{pmatrix}1&1\\0&1\end{pmatrix}\) と置けば
`e=PdP⁻¹` である。従って `B=A⋊_d⟨t⟩` と `C=A⋊_e⟨u⟩` はともに
`S₃×C₃` と同型で、`V(S₃)` に属する。ここでは `t a t⁻¹=d(a)`、`u a u⁻¹=e(a)`
という作用の約束を用いる。固有値 `−1` の1次元空間と `⟨t⟩` が `S₃` を作り、
固有値 `1` の1次元空間が直積因子 `C₃` となる。

もし `B,C` が `A` 上で `H∈V(S₃)` に amalgam したとする。
`A` は `B,C` の両方で正規なので、`⟨B,C⟩` 内でも正規である。
`S₃` の交換子部分群と平方全体はともに `C₃` に含まれるので、恒等式
`[[x,y],z²]=1` が `S₃`、従って `H` で成立する。
`A` の任意の元は `A` 内の平方だから、`[t,u]=tut⁻¹u⁻¹` は `A` を中心化する。
よってその作用 `ded⁻¹e⁻¹` は恒等作用、従って `de=ed` となるはずである。
しかし `𝔽₃` 上で

\[
 de=\begin{pmatrix}1&1\\0&1\end{pmatrix}
 \ne\begin{pmatrix}1&2\\0&1\end{pmatrix}=ed,
\]

となり矛盾する。従って amalgamation property は失敗する。
普遍理論の model companion が quantifier elimination を持つなら amalgamation property が
従うので、この例の通常の群言語の model companion は quantifier elimination を持たず、
model completion でもない。3節の有限 envelope の議論には、全基底での amalgamation
property は必要ない。

## 6. 指数4の full variety について残る境界

指数4の全群の variety `V₄` は、class を2に固定した指数4群の variety とは異なる。
Sanov の定理により `V₄` は局所有限だが、その有限生成群の冪零度に一様上界はない。
具体的には、Razmyslov の
[*On a problem of Hall and Higman*, p.133 の Corollary](https://www.mathnet.ru/php/getFT.phtml?jrnid=im&paperid=1848&what=fullteng)
は `r≥3` に対し `B(r,4)` の class が `3r−2` であることを述べる。
少なくとも `D₈∈V₄` が非可換冪零なので、Olshanskii Lemma 1 により
`V₄=ISP(K)` となる有限 `K` は存在しない。
したがって本ノートの有限 `K` による方法は、`V₄` の model companion の存在を判定しない。

自然な obstruction 候補については、次の短い central product に注意が必要である。
`G∈V₄` と中心 involution `1≠a∈Z(G)` を取る。
`D₈=⟨u,v⟩` の中心 involution を `c=[u,v]` とし、

\[
 L=(G\times D_8)/\langle(a,c^{-1})\rangle
\]

と置く。両群の中心 involution を同一視しているので `G→L` と `D₈→L` は単射である。
例えば `(g,1)=(a^j,c^{-j})` なら `c^j=1`、従って `j` は偶数で `g=1` となる。
直積と商は指数4を保つので `L∈V₄`、そこで `a=[u,v]` が成立する。
従って e.c. な `M∈V₄` の中心 involution はすべて2変数の交換子として表される。
元の部分群の中でだけ測った交換子表示の長さは、そのまま e.c. 群内部の下界にはならない。

同じ構成は lower central series の深さに対しても働く。
各 `c≥1` に対し、十分大きい `r` の `B(r,4)` を `γ_{c+1}` で割れば、class がちょうど `c` の
有限群 `H∈V₄` を得る。その非自明な中心部分群 `γ_c(H)` は位数2の元 `z` を含む。
上の central product で `a` と `z` を同一視すれば、`a∈γ_c(L)` となる。
`z` をパラメータ `a` に指定する `H` の有限 diagram を e.c. 性で `M` に移すと、

\[
 a\in\bigcap_{c\ge1}\gamma_c(M)
 \qquad\text{for every }a\in Z(M)\text{ of order }2
\]

を得る。ここで各 `c` に対して別の有限 diagram を使うので、無限連立条件を一度に
e.c. 性で移しているわけではない。
また、これ自体から e.c. 群の中心 involution の存在は主張していない。

この構成は中心性と位数2を仮定しており、一般の元には適用していない。
全ての深さを単一の有限 diagram や一様な生成元数の群で実現するとも主張していない。
`V₄` の未解決部分で必要なのは、こうした小さい拡大によって
消える障害と消えない障害の区別である。
また、指数3の場合にも有限 absolute retract envelope を一般に期待できないことは
[有限 residual のノート](section-six-finite-residual.md) の central product の議論と整合する。
第6節全体の未解決範囲は [既存の整理](section-six-analysis.md) を参照されたい。
