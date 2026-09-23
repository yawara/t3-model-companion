# v8参考文献再照合: Saracino-Wood 1979 / Maier 1989

確認日: 2026-09-24。今回追加された公刊版PDFを直接読み、前日の原著未入手項目を再確認した。既存監査記録・TeX・Leanは変更していない。

## 結論

**v8の両文献への数学的言及は、公刊版の定理と一致する。**

- Saracino-Wood, Theorem 3.9, p.198 は任意の整数 `2 <= m < infinity` に対する結果。奇素数指数に限らない。原著の `T^m` の定義から nilpotency class **at most 2**、指数恒等式 `x^m = 1`、通常の群言語についての model companion の存在である。
- Maier, Theorem 3.5, pp.285-286 は `K = N_c intersect B^p`、`p` prime、`c < p` について **model companion の存在を直接述べて証明**している。拡大言語の Fraisse limit から後年の論文で初めて得られた結果ではない。
- したがって前日の「SW1979・Maier1989の原著直接照合未完了」は、この2件について解消した。dEMRSの公刊版の番号は今回の担当外。

## 対象と識別情報

| 対象 | SHA-256 |
|---|---|
| `T3_modelcompanion_v8.tex` | `9546045ccd5cb0170ac54fe1485d356765400ed938c57442da558c41c51fa38c` |
| `references/publications/saracino-wood-1979-periodic-existentially-closed-nilpotent-groups-published.pdf` | `0821a6cb5866bae51df4572e05036ca9f76dc357c9f9a297c9eb8a1e001d0060` |
| `references/publications/maier-1989-nilpotent-groups-of-exponent-p-published.pdf` | `4a13a6dba2eadf35423b0c2fe89a6ca10abbd31a89ddb59950d89f4dc3eac63d` |

原頁の意味は誌面印刷頁であり、PDF通し番号ではない。

## Saracino-Wood 1979

原著: D. Saracino and C. Wood, *Periodic existentially closed nilpotent groups*, Journal of Algebra 58 (1979), 189-207. [DOI](https://doi.org/10.1016/0021-8693(79)90199-6)

### 原著の定義・条件・結論

1. **p.189, Introduction:** `T` は群公理に `forall x y z, [[x,y],z]=1` を加えたもの。原著が本文で略して「class 2」と呼ぶ対象は、この定義では厳密に class 2 ではなく **class at most 2** であり、可換群も含む。
2. **同頁:** `T^m = T union {forall x, x^m=1}`。したがって指数が `m` を割るという恒等式の意味である。位数がちょうど `m` の元の存在を別に仮定していない。v8の群 variety の用法と一致する。
3. **pp.190-191, Notation:** `E_m` は `T^m` のe.c.モデルのクラスとして定義。有限個の群の方程式・不等式の解を使ってe.c.性を説明しており、中心やLazard seriesを命名した拡大言語に替えていない。
4. **Theorem 3.9, p.198:** 条件は `2 <= m < infinity`、結論は `T^m` が `aleph_0`-categorical model companion を持つこと。p.198の原頁画像で **下限の <=** を確認した。既存抽出テキストはここを `2 < m` と誤読しているため、引用範囲の判定には原画像を用いる必要がある。
5. **pp.198-200, proof:** 奇素数・2冪の場合を分けた群言語の公理を与え、p.200で任意の `m>1` を素因数分解して公理を組み合わせる。偶数指数を除外する条件はない。p.198で `T^2`、より一般に奇数 `n` に対する `T^(2n)` の2-primary partが可換になる場合も明示的に扱っている。

`m=1` はTheorem 3.9の範囲外だが、自明群の完全理論がそれ自身のmodel companionとなる自明な場合である。v8で主に扱う `n>1` の範囲に不足はない。

### v8との対応

- Abstract lines 102-103: 固定有限指数・class at most 2 のmodel companionの存在。**一致**。
- Introduction line 143: 同上をSWに帰属。**直接引用で一致**。
- line 169: exponent 3のclass 3全体はclass-2結果では覆えない。**引用定理の範囲比較として一致**。
- lines 1473-1474: 同上の反復。**一致**だが `if0` 内の非表示節。

本文を直す必要はない。出典位置を明確にするなら `cite[Theorem 3.9]{SaracinoWood1979}` とできる。

## Maier 1989

原著: B. J. Maier, *On nilpotent groups of exponent p*, Journal of Algebra 127 (1989), 279-289. [DOI](https://doi.org/10.1016/0021-8693(89)90253-6)

### 原著の定義・条件・結論

1. **p.279, Introduction:** `N_c` はclass **at most c** のnilpotent groups、`B^n` はexponent `n` のgroupsと定義。対象(1)は `K=N_c intersect B^p` で、`p` は `c` より大きい素数。
2. 同頁の `K'` はcentral factorの指数を制限する別クラス、`K''` はそのtorsion subclass。v8が述べる純粋なexponent-p群の結果は **K** に対応し、`K'` や `K''` に関する結果と混同していない。
3. **Theorem 1.2, p.281:** `c<p` のもとで、amalgamが `K` 内で実現できることとcoupled central seriesの存在を特徴づける。すべてのamalgamが無条件に実現できるという定理ではない。
4. **Theorem 2.1, p.283:** `K` 内のamalgamation basesはupper/lower central seriesが一致する群として特徴づけられる。これは後のmodel companionの証明で用いられる性質であり、Theorem 3.5の対象クラスを事前にこのsubclassへ狭める追加仮定ではない。
5. **p.285, Theorem 3.5直前:** model companionは、当該クラスのe.c.群をモデルとする一階理論として説明される。
6. **Theorem 3.5, p.285:** `c<p` を仮定し、`K` のcountable e.c. groupの一意性と、`K` が `aleph_0`-categorical model companionを持つことを述べる。countabilityは一意性の結論であり、model companionが対象とする群全体へのcountability仮定ではない。
7. **Proof (2), p.286:** 最初の公理群(I)は群公理、長さ `c+1` の交換子恒等式、`forall x, x^p=1`。著者自身が(I)は `K` をaxiomatizeすると明記している。したがって `B^p` の意味も、`x^p=1` という恒等式で確定できる。
8. **同頁:** 公理(II),(III)は有限群のdiagramを使う一階の公理scheme。diagramとは群表の等式と異なる元を区別する不等式の有限論理積であると説明される。有限群にわたる記号上の量化は有限個の元にわたる量化の略記。**Lazard seriesのpredicateや追加sortはない**。
9. **p.286, proof末尾:** (I)-(III)が `K` のmodel companionとなることを明記している。

### v8との対応

- Abstract lines 103-104: prime p、class at most c<pについてMaierがmodel companionの存在を得た。**Theorem 3.5と直接一致**。
- Introduction line 144: Maierのamalgamationの結果から存在が従う。**正しいが、原著の直接定理を引用する方が明確**。証明は実際にTheorems 1.2, 2.1等を利用するので現行の書き方は誤りではない。
- line 169: `p=c=3` は範囲外。**一致**。
- lines 1475-1478: 同上の反復。**一致**だが `if0` 内の非表示節。

引用改善案（数学的訂正ではない）:

> For prime exponent p and nilpotency class at most c<p, Maier proved that the theory has a model companion [Maier1989, Theorem 3.5]; see also [dEMRS2025, Corollary 4.42].

この形ならpure-group model companionの根拠を、後年の公刊版番号確認に依存せず1989年の原著内で特定できる。

## 確認方法と境界

- SW原頁189,198,199,200、Maier原頁279,285,286を画像で直接確認した。Maierのamalgamation部分は全文抽出テキストでも文脈を通読した。
- この監査はv8での言及と原著の定義・仮定・結論・言語との照合であり、両論文の全証明を再証明したという主張ではない。
- 新規の画像2枚（SW p.199、Maier p.286）は本監査フォルダに保存。他の原頁画像・原PDF・抽出テキスト・前日記録は変更していない。
- TeXやLeanの変更がないため、ビルド・Lean証明監査は実施していない。
