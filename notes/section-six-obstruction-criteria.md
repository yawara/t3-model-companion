# 第6節：有限障害条件と一般論の適用限界

2026-09-22。[第6節の検討](section-six-analysis.md)を補足する文献照合と数学的考察である。
群については一貫して通常の一階群言語 `L_grp={1, ·, ⁻¹}` を使う。
`V` を群 variety、`T_V` をその恒等式による普遍理論とし、e.c. は `V` の中での
existential closedness を意味する。amalgam は指定された底群上で可換する二つの埋込みを持つ
`V`-群であり、二つの像の交わりが底群だけになるという強い条件は課さない。

以下の文献定理の追加形式化、および後半の具体的構成の Lean 証明は行っていない。
既存の Fact 2.6 の形式化と、本ノートの未形式化の議論を区別する。
Question 6.1、Question 6.2、Takeuchi 予想の解決は主張しない。

## 1. Lipparini の有限障害条件

[Lipparini, *Locally finite theories with model companion*](https://www.bdim.eu/item?fmt=pdf&id=RLINA_1982_8_72_1_6_0),
Atti Accad. Naz. Lincei Rend. Cl. Sci. Fis. Mat. Natur., ser. 8, 72 (1982), 6–11、
Theorem 2、pp. 8–9 を、局所有限群 variety と有限群の包含へ特殊化する。
原定理は有限生成 pseudo model と条件 (″) を使うが、この特殊化では通常の有限群で足りる。

`T_V` が model companion を持つことは、各有限 `A≤B∈V` に対して、有限個
`A≤C₁,…,Cₖ∈V` を選べて、次を満たすことと同値である。空のリストも許す。

1. 各 `i` について、`B` と `Cᵢ` は `A` 上で amalgamable でない。
2. 任意の `A≤D∈V` について、`D` と `Cᵢ` がすべての `i` で amalgamable でなければ、
   `D` と `B` は `A` 上で amalgamable である。

条件2は有限 `D` だけについて要求しても同値である。
実際、任意の `D` が各 `Cᵢ` と非 amalgamable なら、compactness によりその障害は
有限生成部分群 `Dᵢ≤D` に現れる。有限個の `Dᵢ` と `A` が生成する有限部分群を `D₀` とする。
`D₀` を含むどの有限部分群も各 `Cᵢ` と非 amalgamable なので、有限版の条件2により
`B` と amalgamable である。再び compactness により `D,B` の amalgam が得られる。
空のリストの場合は `D₀=A` とすればよい。
同定理 (i) の対応する表現は、
任意の e.c. `M∈V` と底群の埋込み `A≤M` について

\[
 B\hookrightarrow_A M
 \quad\Longleftrightarrow\quad
 \text{どの }C_i\text{ も }M\text{ に }A\text{ 上で埋め込めない}
 \tag{L}
\]

となる。有限障害のリストは `A≤B` に依存するが、`M` には依存しない。

条件2を、任意の `D` に対する双方向の同値へ置き換えてはいけない。
例えば `D=A` は `B` とも各 `Cᵢ` とも amalgamable である。
また、`Cᵢ` と `D` が amalgamable であることと、`Cᵢ` が `D` 自身に埋め込めることは
一般には異なる。有限 `Cᵢ` と e.c. `D` の場合は、その有限図式を e.c. 性で実現できるので一致する。

## 2. v7 Fact 2.6 との正確な対応

原稿 [T3_modelcompanion_v7.tex](../T3_modelcompanion_v7.tex) の Fact 2.6、
TeX 293–344、label `fact:locally finiteness and model companion` は、
有限言語の局所有限な `Π₂` 理論について、e.c. モデル内部の障害の生成元数を特徴付ける。
Lipparini の普遍理論への仮定と原稿の `Π₂` 仮定を同一視せず、ここでは両方が適用できる
`T=T_V` に限って比較する。

固定した有限 `A≤B` に対し、Fact 2.6 の上界を `n_{A,B}` とする。
`A` を含み、高々 `n_{A,B}` 元で生成され、`B` と amalgamable でない有限群を、
`A` 上の同型を除いて列挙して `C₁,…,Cₖ` とする。
局所有限性と有限言語の仮定から固定生成元数で位数が一様に有界であり、
さらに有限な `A` の埋込み方も有限個なので、このリストは有限である。

e.c. `M` が `B` を `A` 上で含まなければ、`M,B` は非 amalgamable である。
Fact 2.6 はある `Cᵢ` の `M` への埋込みを与える。
逆に `B,Cᵢ` が両方 `M` に埋め込めれば `M` がその amalgam となり矛盾する。
これで (L) が得られる。

逆に有限リストと (L) があれば、`B,M` が非 amalgamable なとき、ある `Cᵢ` が `M` に入る。
その像を障害部分群とすればよく、全生成元数の上界を
`max({0}∪{d(Cᵢ):1≤i≤k})` と取れる。これは相対的な生成元数ではなく、
Fact 2.6 と同じ、部分群全体を生成する元の数である。

この比較は、第5節の Proposition 5.5 が示す任意モデル内の障害下界とも整合する。
`F_ω` を e.c. `M` に埋め込むと、非 amalgamation は保存されるが、
`M` 内の小さい障害部分群は `F_ω` の外の元を含み得る。
`D≤F_ω` についての生成元数下界は、そのような `D≤M` を制約しない。

## 3. 一般の局所有限代数への拡張は成立しない

[Willard, *Determining whether V(A) has a model companion is undecidable*](https://www.math.uwaterloo.ca/~rdwillar/documents/Publications/mc4.pdf)
の Theorem 9.7 と Corollary 9.8、著者公開版 p. 30 は、有限言語の有限代数 `A` が生成する
`V(A)=HSP(A)` にも model companion を持たない例があり、その有無の判定が
決定不能であることを示す。これは通常の群言語の group variety に限定した結果ではない。

有限代数 `A` について `F_{V(A)}(r)` は `A` 上の `r` 変数 term function の代数と同一視でき、
有限集合 `A^{A^r}` に埋め込める。従って `V(A)` は局所有限である。
このため「局所有限な代数的 variety はすべて MC を持つ」という一般化には実際の反例がある。
Q6.1 を肯定するなら、群に固有の性質を使う必要がある。

同論文 Lemma 2.3、pp. 3–4 の非存在の仕組みも重要である。
各段階で存在的な障害 `θ_n` を e.c. 拡大へ保存し、それが固定の存在式 `ψ` を排除する。
一方、各々の補助条件は有限個の段階を除いて成立する。
e.c. モデルの nonprincipal ultrafilter に関する ultraproduct では全補助条件が成立し、
拡大では `ψ` を実現できるが、
ultraproduct 自身では `ψ` は偽のままとなる。従って e.c. 類は初等的でない。
この機構を群へ移すには、障害が e.c. 拡大後も残ることを含めて具体的に証明する必要がある。
第5節の任意モデル内の生成元数下界だけでは、その入力は揃わない。

## 4. MC、model completion、AP、coherence

[Metcalfe–Reggio, *Model completions for universal classes of algebras: necessary and sufficient conditions*](https://arxiv.org/pdf/2102.01426),
arXiv:2102.01426v2 の次の箇所を参照する。

- Proposition 3.1(c)、p. 7：model companion が存在するとき、それが model completion
  であることと、元のモデル類が AP を持つことは同値である。
- Theorem 3.2／Corollary 3.3、p. 8：特に局所有限 variety では、model completion の存在は AP と同値。
- Proposition 2.4／Remark 2.5、pp. 3–4：variety の coherence は variable projection property と同値で、
  局所有限 variety はすべて coherent。
- Proposition 2.11、p. 5：局所有限 variety は conservative model extension property も持つ。

ここで coherence は、有限表示 member の有限生成部分代数が、その variety に相対的に
有限表示であることをいう。個々の群についての通常の有限表示や、係数を許す方程式系の
equational Noetherianity と同じ定義ではない。

`T₃` は原稿で MC を持つと証明される一方、第5節の非 amalgamation の例が AP を否定する。
従って通常の群言語では model completion を持たない。
この実例は、上記の model completion の特徴付けで MC 自体を判定できないことを示す。

## 5. Equational Noetherianity を必要条件にする経路は使えない

以下は係数を任意のモデルの元から取る通常の意味の equational Noetherianity に関する、
未 Lean 化の直接的な計算である。

`H=UT₃(𝔽₃)` とし、行列単位を用いて `x=I+E₁₂`、`y=I+E₂₃` と取る。
`H` は有限な指数3の群で、`[x,y]≠1` である。
`G=⊕_{i∈ℕ}H` とし、`aᵢ,bᵢ` をそれぞれ第 `i` 座標が `x,y`、他の座標が単位元の元とする。
`G∈V₃` であり、`i≠j` なら `[bᵢ,aⱼ]=1`、一方 `[bᵢ,aᵢ]≠1` である。

一変数の方程式系

\[
 S(t)=\{[t,a_i]=1:i\in\mathbb N\}
\]

の任意の有限部分系 `S₀` に対し、そこに現れない添字 `k` を選ぶと、
`b_k` は `S₀` を満たすが `S` を満たさない。
従って `G` は equationally Noetherian でない。
同じ等式・不等式は任意の群埋込み `G≤E` の下で保存されるので、
`E` の中でも `S` は有限部分系に還元できない。

特に `V₃` 内の e.c. 拡大 `E` を取れる。
原稿の主定理により `T₃` は MC を持つにもかかわらず、この `E` は equationally Noetherian でない。
よって「MC があるなら全 e.c. モデルが equationally Noetherian」という含意は成立しない。
係数なしの方程式系や、有限表示対象に限定した別の有限性条件を否定する主張ではない。

## 6. Residual smallness を必要条件にする経路も使えない

variety が residually small であるとは、その subdirectly irreducible members の濃度に
ある共通の基数上界があることをいう。残余有限性とは異なる条件である。
次の未 Lean 化の構成は、`V₃` が residually small でないことを直接示す。

任意の無限基数 `κ` を取り、

\[
 U=\mathbb F_3^{(\kappa)},\qquad W=U\oplus U,\qquad
 \omega((u,v),(u',v'))=\sum_{i<\kappa}(u_i v'_i-v_i u'_i)
\]

とする。各ベクトルは有限支持なので和は有限であり、`ω` は非退化交代形式である。
集合 `H_κ=W×𝔽₃` に

\[
 (w,z)(w',z')=(w+w',z+z'+2\omega(w,w'))
\]

と積を定める。双線形性から結合律が従い、単位元は `(0,0)`、逆元は `(-w,-z)` である。
交代性から `(w,z)^r=(rw,rz)` なので指数は3を割る。
原稿の交換子規約 `[g,h]=ghg^{-1}h^{-1}` では

\[
 [(w,z),(w',z')]=(0,\omega(w,w')),
 \qquad Z(H_\kappa)=\{0\}\times\mathbb F_3.
\]

最後の中心の等式は `ω` の非退化性から従う。
非自明正規部分群 `N` が中心に含まれる場合、中心の位数が3なので `N=Z(H_κ)`。
中心に含まれない場合は、ある `(w,z)∈N` で `w≠0` がある。
`ω(w,−)` は非零線形写像 `W→𝔽₃` なので全射であり、
`[(w,z),H_κ]=Z(H_κ)≤N` となる。
従って中心は最小の非自明正規部分群で、`H_κ` は subdirectly irreducible である。

`|H_κ|=κ`、かつ `κ` は任意なので `V₃` は residually small でない。
一方 `T₃` は MC を持つ。従って residual smallness も MC の一般的な必要条件にはできない。
特別な部分クラスに対する十分条件として用いる可能性までは排除しない。

## 7. 残る問題の位置

Q6.1 では、局所有限性からは固定生成元数での有限性が得られるが、
Lipparini／Fact 2.6 の e.c. モデル内の有限障害リストそのものを得る入力が残る。
一般代数の反例を通常の群言語へ移したことにはならない。

Q6.2 では、既存ノートの restricted Burnside による還元の後にも、
MC の存在から非恒等式を有限 member で検出できることを導く入力が残る。
coherence、equational Noetherianity、residual smallness を混同してこの入力を補うことはできない。
互いに素な指数の場合の肯定結果の組合せは、別の
[独立な結合のノート](section-six-coprime-joins.md)で扱う。
