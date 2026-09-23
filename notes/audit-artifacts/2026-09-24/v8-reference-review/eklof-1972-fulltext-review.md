# Eklof 1972 単著全文による追加レビュー

日付: 2026-09-24。

対象原著: Paul C. Eklof, *Some model theory of abelian groups*, J. Symbolic Logic **37** (1972), no. 2, 335–342, DOI <https://doi.org/10.2307/2272976>。

利用者提供PDF: `references/2272976.pdf`（表紙を含む9頁、SHA-256 `91fae6e207bab26578c4d961b868a35208725cdf5ef959af8716c6ca71ddc4e7`）。原著全8頁の抽出テキストを読み、不変量の定義とTheorem 4の文p.336、Theorem 7の前半p.339、後半と証明p.340、Remarks p.341はページ画像でも照合した。p.336の独立レンダリングは `references/audit-artifacts/t3-model-companion/2026-09-24/v8-reference-review/abelian-pages/eklof-solo-p336.png`、他の画像は `references/rendered-pages/eklof-1972/` にある。TeX・原著PDF・manifest・主監査報告は変更していない。

## 更新された結論

**v8:133 の数学的命題は、単著論文の Theorems 4 and 7 から導ける。** その導出を以下に記す。これは原著にその形で明記された定理ではなく、今回の監査で明示した系である。

したがって「単著論文はcomplete inductive理論を扱うから、v8のJEP版は支えられない」と打ち切るのは強すぎる。Theorem 7単独の結論は確かにcomplete理論についてだが、Theorem 4の普遍理論分類と組み合わせれば、不完全な理論にも対応できる。

**ただし、v8の帰属先 Eklof–Fischer, Ann. Math. Logic 4 (1972), 115–171 は修正が必要。** 保持できるのは一般命題の内容であり、「Eklof and Fischer proved」という現在の直接帰属ではない。引用をEklof単著のTheorems 4 and 7へ替え、「これらから従う」と明記し、下の導出を短く添えるのが正確である。

本メモは、同日の `abelian-review.md` における「追加論証が必要」という境界を、実際にその追加論証を与えることで更新する。元のEF文献との不一致という指摘は維持する。

## 原著が直接述べる結果

- **Theorem 4, pp.336–338**: アーベル群B,Cについて、Bの全普遍文がCでも真であることを、有限指数の条件と `dim((p^n B)[p]) >= dim((p^n C)[p])`（有限値または∞として比較）で特徴付ける。
- **Theorem 7, pp.339–340**: 任意のアーベル群Aについて、`Th(A)` がinductive、`Th(A)` がmodel complete、および次のSzmielew不変量条件は同値。
  1. 各pで `D(p;A)=∞` なら全nで `U(p,n;A)=0`。
  2. `U(p,n;A)=∞` ならm<nで `U(p,m;A)=0`。
  3. 各pで `Tf(p;A)=0`。
- **Remarks, p.341**: Dedekind整域上の加群への一般化、他の加群結果、完全理論のAPの特徴付け、Theorem 7対象の明示的∀∃公理。v8のinductive+JEP定理そのものは明記されていない。

Theorem 7の冒頭は `Let A be an abelian group`、対象は常に完全理論 `Th(A)` である。ここは前回の抄録読解と一致する。

## Theorems 4 and 7 からの導出

以下の論証は原著の逐語的引用ではなく、上の二定理を使った本監査の数学的導出である。

### 1. 任意のアーベル群Aと普遍同値なmodel-complete群Cを作る

`G[p]={x in G : px=0}` とし、`(p^nG)[p]` は `p^nG` のp-torsionを表す。`p^n(G[p])` ではない。

各素数pに対し

\[
d_{p,n}=\dim_{\mathbf F_p}((p^nA)[p])\in\mathbf N\cup\{\infty\}
\]

と置く。無限次元の値はすべて∞で記録する。この列はnについて非増加である。

**場合I: 全てのnで `d_{p,n}=∞`。**

\[
C_p=\mathbf Z(p^\infty)^{(\aleph_0)}.
\]

**場合II: 有限値の項が存在する。** 最初の有限項の添字をNとする。n≥Nでは非増加の自然数列なので、ある有限値dで安定する。n≥Nに対し `u_n=d_{p,n}-d_{p,n+1}` と置く。u_nが正の箇所は有限個である。

\[
C_p=\mathbf Z(p^\infty)^{(d)}
\oplus E_p
\oplus\bigoplus_{n\ge N}\mathbf Z(p^{n+1})^{(u_n)},
\]

ただし、N=0なら `E_p=0`、N>0なら

\[
E_p=\mathbf Z(p^N)^{(\aleph_0)}.
\]

この定義で有限値同士の差しか取っておらず、`∞-∞` は使用していない。

全素数についての直和を `C_0=⊕_p C_p` とし、Aが有限指数ならC=C_0、Aが有界指数でないなら `C=C_0⊕Q` とする。

**普遍理論が一致すること。** 位数p^kの巡回因子は、n<kのとき `(p^nC_p)[p]` に次元1を寄与し、n≥kでは0を寄与する。Prüfer因子はすべてのnで次元1を寄与する。したがって場合IIで、n≥Nなら

\[
\dim((p^nC)[p])=d+\sum_{k\ge n}u_k=d_{p,n};
\]

n<Nなら `E_p` によって次元∞となる。場合Iも明らかに全て∞である。異なる素数のprimary成分とQはp-torsionに寄与しない。よって全p,nでAとCのこの次元は一致する。

Aの指数が有限eなら、pがeを割らない場合はC_p=0であり、pがeを割る場合も、全巡回因子の指数は `p^{v_p(e)}` 以下でPrüfer因子はない。従ってCの指数はeを割る。さらに最高の非零p-heightの一致から、Aの指数を最小のeで取ればCの指数も正確にeとなる。Aが有界指数でない場合はQを加えたのでCも有界指数でない。このためTheorem 4を双方向に適用でき、

\[
\operatorname{Th}_{\forall}(A)=\operatorname{Th}_{\forall}(C)
\]

を得る。

**Cがmodel completeであること。** 各pについて、C_pのreduced partは有界p指数であり、他のq-primary成分（q≠p）とQはp-divisibleだから `Tf(p;C)=0`。場合Iでは `D(p;C)=∞` かつ全nで `U(p,n;C)=0`。場合IIでは `D(p;C)=d<∞`、無限のUが現れる可能性はN>0のときのn=N−1だけで、それより低いUは全て0である。n≥NのUは有限なu_nである。

従ってTheorem 7(b)の全条件が成立し、`Th(C)` はmodel completeである。

### 2. JEPから一つの群Aに普遍理論を集約する

Tをアーベル群の言語における無矛盾な理論でJEPをもつものとする。Tと両立する全てのexistential sentencesの集合をΣとする。

Σの任意の有限部分について、各文を満たすTモデルを選ぶ。JEPを有限回適用し、existential sentencesが埋込みで上方保存されることを使うと、有限部分全部を満たすTモデルが得られる。compactnessにより

\[
A\models T\cup\Sigma
\]

を取れる。

任意の普遍文σについて、Tがσを含意すればAもσを満たす。Tがσを含意しなければexistential文¬σはTと両立するのでΣに属し、Aはσを満たさない。従って

\[
T_{\forall}=\operatorname{Th}_{\forall}(A).
\]

### 3. model companionを得る

第1段階でこのAからCを構成し、`T*=Th(C)` と置く。T*はmodel completeであり

\[
T^*_{\forall}=T_{\forall}
\]

である。同じ普遍帰結をもつ理論のモデルは、互いに他方のモデルへ埋め込める（diagramとcompactness）。よってT*は通常の定義でTのmodel companionとなる。

さらにv8のようにTがinductiveなら、T*はTを含意する。実際、`N⊨T*` をTモデルMへ埋め込み、MをT*モデルN'へ埋め込む。像を取り直して `N⊆M⊆N'` としてよい。T*のmodel completenessにより `N≺N'`。Tの各∀∃公理とN内の任意のパラメータについて、Mで取った量化子なしの証人はN'でも証人なので、elementarityによりNにも証人がある。従ってN⊨Tである。これはES1971のinductive理論に対する定義（包含T⊆T*も要求）とも整合する。

これで**v8が述べるinductive+JEPの命題が証明される**。この導出は実は普遍理論の意味でのmodel companion存在についてはinductive仮定を必要としないが、v8を強める編集は本監査では提案しない。

## 原稿で採用できる正確な文言

現在の一般命題を保持するなら、例えば次のように直接帰属と導出を区別する。

```tex
More generally, every inductive theory of abelian groups with the joint
embedding property has a model companion. This follows from Eklof's
criteria for universal equivalence and model completeness
\cite[Theorems~4 and~7]{Eklof1972}.
```

この形なら、上記構成の短い説明または補足補題を付すことが望ましい。JEPで普遍理論を一つのAに集約し、同じp-height次元をもつmodel-completeなCへ置換する、という二段階が核心である。

**原著に直接書かれた定理だけを紹介したい場合**の短い文言は次。

```tex
Eklof proved that a complete theory of abelian groups is model complete
if and only if it is inductive\cite[Theorem~7]{Eklof1972}.
```

こちらは別の内容への置換であり、元の一般命題が誤っているから必要というわけではない。

正しい書誌はEklof単著、JSL37(1972), 335–342、DOI 10.2307/2272976。Eklof–Fischerの共同論文とは区別する。

## 検証境界

- 原著のTheorems 4 and 7を読んで上記有限/∞の全場合を点検した自然言語の数学的導出である。
- 原著にJEP版が明記されている、または当該導出を著者が明記しているとは主張しない。
- Lean形式化や新規のコード検証は行っていない。文献レビューのために不要な既存ライブラリ変更やビルドは行っていない。
