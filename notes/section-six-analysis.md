# v7 第6節の検討と形式化境界

> v8 では旧第6節は非出力となり、Takeuchi 予想は Conjecture 1.1 として序論に残る。このノートはアーカイブした v7 第6節の検討を保存する。

2026-09-22。対象は [T3_modelcompanion_v7.tex](../archives/T3_modelcompanion_v7.tex)
第6節、特に Questions 6.1–6.2 と Takeuchi 予想である。
本ノートは、実装済みの既知の還元、参照文献の適用範囲、今後必要な数学的入力を区別する。
一般の質問への肯定・否定を新たに証明したという主張はしない。

## 1. 今回の Lean 実装で証明される範囲

[Free/Burnside.lean](../T3/GroupTheory/Free/Burnside.lean) は、任意の指数 `n` に対する
相対自由群 `T3.Burnside n I`、その生成元、指数則、生成写像の普遍性と全射性を実装する。
`T3.Burnside.finite_of_fg` は、すべての正の有限 rank の自由 Burnside 群が有限なら、
指数 `n` の任意の有限生成群が有限であることを証明する。

[ModelTheory/Burnside.lean](../T3/ModelTheory/Burnside.lean) の
`T3.exponentGroupTheory_isLocallyFinite_iff_finite_burnside` は、通常の一階群言語で

\[
  T_n\text{ が局所有限}
  \quad\Longleftrightarrow\quad
  \forall r\geq 1,\ B(r,n)\text{ が有限}
\]

を証明する。逆向きは有限生成部分群への全射を使い、順向きは自由生成元集合の閉包に
局所有限性を適用する。空の生成族も実装上処理されている。
これは原稿第6節の既知の還元であり、model companion に関する一般の含意ではない。

Question 6.1、Question 6.2、Takeuchi 予想は対応表で `open` として保持する。
この境界を越える Lean 定理、仮定を隠した定理、未証明 stub は追加しない。
原稿の「十分大きい素数に対する別論文での結果」も、このリポジトリでの証明済み結果には数えない。

## 2. Question 6.1：局所有限性から何が得られるか

局所有限な群 variety `V` では、相対自由群 `F_V(r)` が各有限 `r` で有限であり、
`r` 元生成群はその商なので、位数は `|F_V(r)|` 以下になる。
したがって固定された生成元数では有限群の同型型も有限個しかない。
しかし、amalgamation の失敗を検出する部分群の生成元数 `r` 自体は、この議論では抑えられない。
Fact 2.6 が要求するのは、e.c. モデルの内部での、この追加の一様性である。

第5節の `A_n ≤ F_ω` は、この違いを具体的に示す。底群は常に位数3・生成元数1で、
他方の因子も固定した `F_3` なのに、`F_ω` 内部の障害には少なくとも `2n` 個の生成元が必要となる。
従って、任意モデルに対する局所有限性だけから一様な障害上界を得る経路は使えない。

この例を e.c. モデルへの反例に移すこともできない。`F_ω` を e.c. 群 `M` に埋め込むと、
非 amalgamation 自体は保存されるが、`M` 内で新たに得られる小さい障害部分群は
`F_ω` の外の元を含み得る。第5節の下界は `D ≤ F_ω` に対するものであり、
そのような `D ≤ M` に適用することはできない。

検討する価値のある経路は、指数3の証明で使う次の役割を、候補となる variety ごとに分けることである。

1. e.c. 群の内部で、有限底群を生成元数の一様に有界な有限部分群へ拡張する構成。
2. その部分群の包含が、必要な有限因子との coproduct の比較写像を単射にする性質。
3. 関係式の正規閉包への所属を、有界な個数の生成元を持つ部分群に移す support の評価。

指数3では第4節と第3節がこれらを供給する。一般の局所有限 variety については、
有限群の列挙だけではいずれの内部構成も供給できない。
e.c. モデルの ultraproduct が再び e.c. だと仮定して一様性を導く議論も、
ここで確立すべき elementary 性を先取りするため、そのままでは証明にならない。

## 3. 関連する存在定理の適用範囲

[d'Elbée–Müller–Ramsey–Siniora, arXiv:2310.17595v3](https://arxiv.org/html/2310.17595v3)
の §4.1 冒頭は素数 `p > c` を仮定する。同論文 Corollary 4.42 は、
Lazard series の述語を除いた**通常の群言語**でも、class が高々 `c`、指数 `p` の群の理論に
model companion があると述べる。したがって、拡大言語だけの結果として扱うのも、
`c < p` を外して適用するのも正しくない。特に `c = p = 3` はこの適用範囲に含まれない。
刊行版は J. Algebra 662 (2025), 640–701、
[doi:10.1016/j.jalgebra.2024.08.012](https://doi.org/10.1016/j.jalgebra.2024.08.012) である。

[Burris, “Model companions for finitely generated universal Horn classes”](https://www.math.uwaterloo.ca/~snburris/htdocs/MYWORKS/PAPERS/Model%20Companions.pdf),
J. Symbolic Logic 49 (1984), 68–74、Theorem 1.1 は、有限個の有限構造 `K` が生成する
universal Horn class `ISP(K)` の model companion の存在を述べる。
ここで `I,S,P` は同型、部分構造、直積による閉包である。
これは群 variety を与える `HSP(K)` の主張ではなく、準同型像の閉包 `H` を追加して
そのまま使うことはできない。適用には対象の variety と該当する `ISP(K)` の一致など、
別の証明が必要となる。従ってこの定理だけから Question 6.1 は解決しない。
[刊行情報と abstract](https://doi.org/10.2307/2274092) も確認できる。

## 4. Question 6.2：restricted Burnside による還元

以下は、既知の restricted Burnside theorem を使った数学的整理であり、
**今回の Lean 実装には含めていない**。RBP を project axiom として導入することもしない。

正整数 `e` に対して恒等式 `x^e = 1` を満たす群 variety `V` を固定する。
`Fin(V)` をその有限 members の類とする。このとき、次の条件は同値である。

1. `V` は局所有限である。
2. 各正の有限 `r` について、相対自由群 `F_V(r)` は残余有限である。
3. `V` の恒等式は `Fin(V)` の恒等式と一致する。

条件3は、恒等式による variety 生成の意味で `V = HSP(Fin(V))` と言い換えられる。
これは有限個の有限群による生成を意味せず、前節の Burris の `ISP(K)` とも異なる。

**証明スケッチ。** 1から2は、有限な相対自由群が残余有限であることによる。
1から3は、恒等式に反する代入の値が有限個であり、それらが生成する部分群が有限であることによる。
3から2について、`F_V(r)` の非単位元を群語 `w` で表す。
`w = 1` は `V` の恒等式ではないので、3により有限 `H ∈ V` で非自明な値を取る。
相対自由群の普遍性が、その元を分離する有限群への準同型を与える。
逆に2から3も、非恒等式を相対自由群で評価し、有限商へ分離することで従う。
有限商は variety `V` に留まる。

2から1には深い外部結果が必要となる。restricted Burnside theorem は、
固定した `r,e` に対して有限 `r` 元生成・指数が `e` を割る群の位数に上界 `N(r,e)` を与える。
残余有限な `r` 元生成・指数 `e` の群に `N(r,e)+1` 個の相異なる元があれば、
各対を分離する有限商を有限個選び、その直積への像を取る。
その像は指数が `e` を割る有限 `r` 元生成群であり、選んだ元はすべて相異なるままなので、
位数上界に矛盾する。従って `F_V(r)` は有限であり、その商である任意の
有限生成 `V`-群も有限となる。

RBP の主要原典は Zel'manov の
[奇指数の場合](https://www.mathnet.ru/eng/im1104)
(Math. USSR-Izv. 36 (1991), 41–60) と
[2群の場合](https://www.mathnet.ru/eng/sm1311)
(Math. USSR-Sb. 72 (1992), 543–565) である。
一般指数への適用には Hall–Higman の還元と有限単純群の結果を含む標準的な還元も用いる。
この区別は著者自身の
[“Recent Progress in Algebra”, p. 238](https://sites.lsa.umich.edu/idolga/wp-content/uploads/sites/1334/2024/08/korea98.pdf)
の RBP の説明とも整合する。ここではこれらの深い証明を再検証・形式化したとはしない。

この還元により Question 6.2 の不足は、次の含意に集中できる。

\[
 T_V\text{ が model companion を持つ}
 \quad\Longrightarrow\quad
 \text{各非恒等式を有限 }V\text{-群で検出できる}.
\]

model companion が与える e.c. モデルとの universal theory の一致は、
有限 members へのこの移送を直接には与えない。本ノートではこの含意を証明していない。
残余有限性を追加仮定して局所有限性を得ても、Question 6.2 全体の解決にはならない。

## 5. 今後の作業に用いる区別

第6節の既知の Burnside 還元の形式化は、一般の二つの質問の解決とは独立に完了できる。
Takeuchi 予想についても、局所有限性と自由 Burnside 群の有限性の同値を証明しただけでは、
model companion の存在との同値を証明したことにはならない。

文献確認では、d'Elbée ほかの §4.1 と Corollary 4.42 の本文、Burris の Theorem 1.1 と
`ISP(K)` の定義を確認した。RBP 原典の書誌と著者の還元説明も参照したが、
原典の深い証明全体の監査を行ったという意味ではない。
新しい主張を実装する際は、上記の未証明入力を仮定として隠さず、その供給を先に確認する。

## 6. 追加検討：具体的な肯定例と、使えない一般化

同日、第6節をさらに検討し、以下を別ノートへまとめた。
いずれも通常の数学的証明・文献による結果であり、新しいLean定理として登録したものではない。
Questions 6.1、6.2、Takeuchi予想の一般形は引き続き未解決として扱う。

1. [有限A-groupのvariety](section-six-a-groups.md)。OlshanskiiとBurrisの定理を
   組み合わせることで、Sylow部分群がすべて可換な有限群が生成するvarietyに
   model companionがあると分かる。`S₃,A₅` は具体例である。
   さらに `V=ISP(K)`、`K` が有限・centerless・monolithicなら、e.c. 群内部の
   `n` 元生成部分群を `E≅K^r`、`r≤|K|^n` に拡張できる。
   `E` はこのvarietyでabsolute retractとなるため、amalgamationの障害を
   `d(E)≤d(K)|K|^n` という明示的な上界で証言できる。

2. [有限商での検出とretractの限界](section-six-finite-residual.md)。
   e.c. 指数3群 `M` は `1≠Z(M)≤R_fin(M)` を満たすことを、明示的な
   Heisenberg群とのcentral productから証明した。
   従って「MCがあるからe.c. 群自身が残余有限」は誤りである。
   また非自明有限指数3群は、有限な指数3拡大だけを考えてもabsolute retractではない。
   上の有限retract構成をそのままQuestion 6.1全体へ拡張する経路は使えない。

3. [互いに素な指数の独立な結合](section-six-coprime-joins.md)。
   指数が互いに素な `V,W` について、`V∨W` がMCを持つことと、両者がMCを
   持つことは同値である。中国剰余定理による定義可能な射影と、有限直積の
   論理式の分解から証明する。`V₂∨V₃` は肯定例だが、`S₃` を含まないので
   指数6群すべてのvariety `V₆` とは異なる。

4. [障害の有限リストによる判定](section-six-obstruction-criteria.md)。
   Lippariniの必要十分条件を、群言語とv7のFact 2.6に合わせて整理する。
   一般の局所有限なalgebraic varietyにはMCのない例があるため、群の構造を使う
   入力が必要である。coherence、equational Noetherianity、residual smallnessを
   混同してMCの必要十分条件とする経路も区別する。

Question 6.1で残る中心的な課題は、有限retractを要求せずに、amalgamationの障害を
有限部分群へ移す仕組みを一般のe.c. 群の中で作れるか、という点である。
指数3のlower-central strictnessはその一例だが、一般varietyで同じ役割を持つ
条件とその内部での構成は、まだ得られていない。

Question 6.2では、e.c. 群全体の残余有限性を経由する案は除外された。
必要なのは有限rankの相対自由群の有限商、同値に非恒等式を有限memberで検出することである。
この有限検出性をmodel companionの存在から導く含意は、今回も証明できていない。

今回の追加ノートは独立に数学的検算を行ったが、Leanによる検証とは区別する。
原稿・数学ライブラリ・paper mapの証明状態は変更していない。
2026-09-22に `python3 scripts/check.py` を再実行し、全チェックが警告ゼロで通過した。
