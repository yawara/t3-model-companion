# v8 参考文献と本文の数学的主張の照合

確認日: 2026-09-23。対象: `T3_modelcompanion_v8.tex`。
SHA256: `9546045ccd5cb0170ac54fe1485d356765400ed938c57442da558c41c51fa38c`。

## 更新（同日、原文取得後の追記）

保留だった 4 文献の原著全文（Eklof–Fischer 1972、Eklof–Sabbagh 1971、Saracino 1974、
Maier 1989）をオープンアクセス版（AMS 誌 PDF の Internet Archive 保存版、Elsevier
open archive の CORE ミラーの Internet Archive 保存版）から取得し、照合を完了した。
統合レポートと証拠ファイルは
[audit-artifacts/2026-09-23/v8-reference-review/README.md](audit-artifacts/2026-09-23/v8-reference-review/README.md)
にある。結果の要点:

- **133行、Eklof–Fischer (1972): 不一致（誤帰属）。** 原著 57 頁の全文に、model
  companion・inductive theory・joint embedding property に関する定理は存在しない
  （§0–§5 は飽和可換群の構造、初等埋め込み、決定可能性、量化記号消去、Dedekind 環上の
  加群）。最も近い既刊結果は P. C. Eklof, *Some model theory of abelian groups*, JSL 37
  (1972) 335–342 の「complete な inductive theory は model complete なものと一致する」で、
  JEP 版の主張はどの文献にも見つからなかった。修正案は README.md の Finding 1。
- **138行、Saracino (1974): 直接一致。** Theorem 1「任意の n ≥ 2 について可解長 ≤ n の
  群の理論に model companion はない」。
- **144行、Maier (1989): 直接一致。** Theorem 3.5 (c < p) が K = N_c ∩ B^p の可算
  existentially closed 群の一意性と ℵ0-categorical な model companion の存在を示す。
  Theorem 1.2/2.1 はアマルガム実現の判定条件と amalgamation base の特徴付けで、K 自体は
  amalgamation property を持たない。「follows from Maier's amalgamation results」は妥当。
- **非表示1502行および136行の出典、Eklof–Sabbagh (1971): 直接一致。** Theorem 2.4
  （可換群の理論の model companion）、Theorem 7.17（全群の理論に model companion なし）。
- **143行、Saracino–Wood (1979): 直接一致。** 利用者提供の出版社版 PDF（2026-09-23）で
  Theorem 3.9 (p. 198)「2 ≤ m < ∞ について T^m は ℵ0-categorical な model companion を持つ」
  を確認（描画頁を目視）。T^m は p. 189 で class 2 冪零群かつ指数 m の理論と定義され、証明は
  p = 2 の場合を別公理で扱うので偶数指数も含む。Maier 1989 の引用 [12, Theorem 3.9]、
  zbMATH レビュー、dEMRS Remark 4.43 とも整合。
- 利用者提供の出版社版 PDF 4 件（Eklof–Sabbagh 1971、Eklof–Fischer 1972、Saracino–Wood
  1979、Maier 1989）は `references/publications/` に安定名で登録し、一次抽出テキストと
  重要頁の 180 DPI 描画を保存した（MANIFEST 16–21 節。Saracino 1974 の AMS 版と Takeuchi
  2022 の RIMS 版も同時に登録）。Eklof–Fischer の誤帰属は出版社版でも再確認した
  （全 57 頁に該当語なし、p. 116 の結果一覧にも該当定理なし）。
- dEMRS の公刊版番号照合は未了（出版社・AUC リポジトリとも HTTP 403）。

以下は追記前の記述で、上記 5 件の「保留」は解消済みとして読むこと。

## 判定

直接確認できた出典の主張は、下記の階数限定の省略を除き、v8と一致する。
ただし全件の原文照合は完了していない。現在表示される本文が引用する12文献のうち、
8文献は原著本文・著者版・原著abstract・原著の公開抜粋のいずれかで該当主張を確認した。
残る4文献は、引用対象の原文を入手してから最終判定する。

参考文献欄は13件。Eklof–Sabbagh (1971) の唯一の引用は、1464–1547行の
`\if0 ... \fi` 内にあるため、現在のPDF本文には出ない。
この文献もソースに残る引用として監査対象に含めたが、原文未入手である。
引用の出現位置は [機械抽出一覧](audit-artifacts/2026-09-23/v8-reference-review/citation-inventory.json) に保存した。

このレビューは、引用先の数学的主張とv8による紹介の一致を検査したもの。
引用先の全証明の独立再検証、v8の主定理の再証明、Leanの再監査を意味しない。
TeX・PDF・Leanは変更していない。

## 具体的な修正候補

### 1. Ivanov の無限性には階数の限定を明記する

v8 **183行**は、十分大きい素数について自由Burnside群が無限とだけ述べる。
[Ivanov (1992), Theorem A(a)](https://arxiv.org/html/math/9210221v1) は
`m > 1`, `n >= 2^48` の下で `B(m,n)` が無限であるという主張。
`B(1,p)` は位数pの巡回群なので、現状の文には階数の限定を補うのが正確である。
局所有限性を否定する用途には階数2だけで十分。

```tex
The free Burnside groups $B(2,p)$ are infinite for all sufficiently large
primes $p$ \cite[Theorem~A(a)]{Ivanov1992}, so this shows the conjecture
for all sufficiently large primes.
```

これは軽微な限定の補足であり、導入部の論旨を変えるものではない。
1992年は正しい。1992年の研究速報と1994年の完全証明論文は別の文献である。
また、182行のmodel companion非存在は著者らの別論文の予告であり、
Ivanovに帰属されているのは183行の群の無限性だけである。

### 2. 表現と出典の所在を精密にできる箇所

- **138行、Saracino (1974)**: 原著取得後、`for every n >= 2, ... derived length at most n`
  と明記するのがよい。現在の `fixed derived length at least 2` は、
  固定された上界nを指すのか、長さがちょうどnなのかが曖昧。現時点で誤った定理と判定するものではない。
- **147行、HKTY**: `some semisimple algebraic groups` は過剰主張ではない。
  より具体的には、model-complete field K 上の split semisimple algebraic group G の
  有理点群 G(K) と書ける。Theorem 3.3 を付すと追跡しやすい。
- **609行、LW1933**: `Satz 1, pp. 156–157` を引用に添えられる。
- **ES1971**: 参考文献には掲載されるが、現在のPDF本文では未引用。
  残す意図なら、132行の可換群の説明に引用を移す方法がある。ただし原著照合後に判断する。
- HKTYの2023年、FKの2025年は初版年として正しい。
  今回読んだ版はそれぞれv2（2025-03-02）、v2（2026-02-08）なので、版の明記は再現性を改善する。

## 全13文献の照合表

「直接一致」は該当主張の一致を意味し、原著全体の証明確認を意味しない。
abstract・公開抜粋だけで確認した場合も、下表にその境界を記載する。

| 文献 | v8の箇所 | 原文の所在・検査した内容 | 判定 |
| --- | --- | --- | --- |
| Chang–Keisler (1990) | 136行 | 第3版 p.199, Example 3.5.16 の公開本文抜粋。「全群の理論にmodel companionはない」と例番号を確認。証明全頁は未取得。 | 直接一致 |
| d’Elbée–Müller–Ramsey–Siniora (2025) | 144行。非表示1478行にも反復 | arXiv v3, Cor.4.42, pp.33–34。素数p、c<pの群の理論のmodel companion。通常の群言語であることまで明記。 | 著者版で直接一致。公刊版の番号照合は残る |
| Eklof–Fischer (1972) | 133行 | 原著全文（Ann. Math. Logic 4, 115–171）を取得し全頁を検索。model companion・inductive・JEP に関する定理は存在しない。最近接は Eklof, JSL 37 (1972) の complete inductive theory = model complete。 | **不一致（誤帰属）** |
| Eklof–Sabbagh (1971) | 非表示1502行のみ | 原著全文 Theorem 2.4（可換群の理論の model companion＝model completion）、Theorem 7.17（全群の理論に model companion なし。Chang–Keisler Example 3.5.16 の原典）。 | 直接一致。現在のPDF本文では未引用 |
| Frącek–Kowalski (2025) | 147行 | arXiv v2, Thm.3.6, p.10。任意の体Kについて、Kのmodel completenessと3次Heisenberg群H(K)の純群言語でのmodel completenessが同値。 | 直接一致。標数の条件漏れなし |
| Hoffmann–Kowalski–Tran–Ye (2023) | 147行 | arXiv v2, Thm.3.3, p.18。model-complete field上のsplit semisimple群の有理点群、およびその交換子群。 | 直接一致。someという限定は適切 |
| Ivanov (1992) | 183行 | 著者版p.2, Thm.A(a)。m>1, n>=2^48のB(m,n)の無限性。 | 大素数の主張を支持。階数限定を補う |
| Levi–van der Waerden (1933) | 167、609–617行 | 公刊原文pp.155–157、(5)、(6)、(8)、Satz 1。class<=3と鋭さ、位数、一意正規形、交換子の規約、添字。 | 直接一致 |
| Maier (1989) | 144行。非表示1476行にも反復 | 原著全文 Theorem 3.5 (c < p): K = N_c ∩ B^p に一意な可算 e.c. 群と ℵ0-categorical な model companion。Theorem 1.2/2.1 が amalgamation の判定条件と amalgamation base の特徴付け。 | 直接一致 |
| Saracino (1974) | 138行 | 原著全文 Theorem 1: 任意の n ≥ 2 について可解長 ≤ n の群の理論に model companion はない。脚注 (2) で class ≤ c の冪零群にも言及。 | 直接一致 |
| Saracino (1976) | 139行。非表示1481行にも反復 | 出版社掲載の原著abstract。各c>=2についてclass<=cの群およびtorsion-free版の双方でmodel companion非存在と明記。 | abstractで直接一致。証明・定理番号は未確認 |
| Saracino–Wood (1979) | abstract、143行。非表示1473行にも反復 | 出版社版全文 Theorem 3.9 (p. 198): 2 ≤ m < ∞ について T^m（class 2 冪零群、指数 m）に ℵ0-categorical な model companion。定義は p. 189。 | 直接一致 |
| Takeuchi (2022) | 137、172行 | RIMS原文Thm.17、PDF p.5（公刊pp.79–84中のp.83）。torsion-free群の非存在を明記。導入PDF p.2（公刊p.80）は固定指数とBurnside問題の関連を言及。 | 直接一致 |

書誌については、取得した原著・著者版・出版社・DOI登録情報を比較した範囲で、
著者、標題、年、巻、頁、識別子の取り違えは見つからなかった。

## 仮定と結論について確認した要点

### 群の言語と補助構造の区別

dEMRSのFraïssé構成はLazard seriesを命名した言語を使うが、Corollary 4.42の
結論は群のreductの理論がmodel companionになるというもの。
Proposition 4.41とその後の議論で補助述語を扱っており、v8の通常の群言語への
引用は正しい。HKTYとFKも最終結論は純群言語であり、定数を追加した構造だけの結果ではない。

### 指数と冪零階数の範囲

SW1979の任意有限指数の主張は、dEMRS Remark 4.43による歴史的帰属までは確認した。
その後の奇素数についての簡単な公理系と、任意有限指数の存在結果は区別されている。
ただしSW原著を確認済みとすることはできない。

素数指数p、階数c<pという既存結果はc=p=3を含まない。
LWの原著からclass 3の指数3群が存在することも確認できるため、
v8がこれら2種類の既存結果の適用範囲外にあると述べる比較は正しい。

### LWの正規形

原著はv8と同じ `aba^{-1}b^{-1}`、左結合の三重交換子を採用する。
添字を1始まりから0始まりに変更すれば、そのままv8の式になる。
位数は `3^(r + binom(r,2) + binom(r,3))`。符号の補正は不要。
無限生成の場合を述べる619–629行は有限生成の原著定理からの帰結であり、
v8でも別のRemarkとして区別されている。

### Takeuchi予想の帰属

Takeuchi2022は固定指数とBurnside問題の関連を指摘しているが、
v8のif-and-only-if予想を明記してはいない。
v8は172行で過去の関連の指摘、173行以降で今回の具体的な予想を分けているため、
2022年文献に完全な予想の定式化があると誤って帰属してはいない。

## 原文取得をお願いしたい文献

### 現在の本文の直接照合に必要だった4件（すべて取得・照合済み。README.md 参照）

1. **P. C. Eklof and E. R. Fischer**, *The elementary theory of abelian groups*,
   Ann. Math. Logic **4** (1972), no.2, 115–171。
   [DOI](https://doi.org/10.1016/0003-4843(72)90013-7)。
   確認対象: inductive + JEPからmodel companion存在を得る定理と、その仮定・定義。
   定理番号は未特定なので全文が望ましい。優先度が最も高い。
   **→ 取得済み。該当定理は存在しない（誤帰属）。**
2. **D. Saracino**, *Wreath products and existentially complete solvable groups*,
   Trans. Amer. Math. Soc. **197** (1974), 327–339。
   [DOI](https://doi.org/10.1090/S0002-9947-1974-0342391-5)。
   確認対象: 各n>=2の可解長上界nに対するmodel companion非存在の定理。
   **→ 取得済み。Theorem 1 で確認。**
3. **D. Saracino and C. Wood**, *Periodic existentially closed nilpotent groups*,
   J. Algebra **58** (1979), no.1, 189–207。
   [DOI](https://doi.org/10.1016/0021-8693(79)90199-6)。
   確認対象: 任意有限指数、class<=2の存在定理。偶数指数を含む範囲と記号の定義。
   **→ 取得済み（利用者提供の出版社版）。Theorem 3.9 で確認。**
4. **B. J. Maier**, *On nilpotent groups of exponent p*,
   J. Algebra **127** (1989), no.2, 279–289。
   [DOI](https://doi.org/10.1016/0021-8693(89)90253-6)。
   確認対象: p>cのamalgamation定理、群と付加filtrationの条件、model companionへの帰結の位置づけ。
   **→ 取得済み。Theorem 1.2、2.1、3.5 で確認。**

### 補足2件

- **d’Elbée–Müller–Ramsey–Siniora**, *Model-theoretic properties of nilpotent groups and Lie algebras*,
  J. Algebra **662** (2025), 640–701。
  [DOI](https://doi.org/10.1016/j.jalgebra.2024.08.012)。
  arXiv v3の該当内容は取得・確認済み。公刊版のCorollary 4.42という番号と内容の同一性を確認したい。
- **P. C. Eklof and G. Sabbagh**, *Model-completions and modules*,
  Ann. Math. Logic **2** (1971), no.3, 251–295。
  [DOI](https://doi.org/10.1016/0003-4843(71)90016-7)。
  現在は非表示部分だけの引用なので優先度は低い。可換群への適用とmoduleのmodel completion定理を確認したい。
  **→ 取得済み。Theorem 2.4、7.17 で確認。**

Saracino1976の本文全体も未取得だが、今回照合する仮定と結論は原著abstractだけで
明記されているため、上の優先取得リストには含めない。

## 証拠と詳細ノート

- [統合レポート（原文取得後）](audit-artifacts/2026-09-23/v8-reference-review/README.md)

- [群論の古典的結果](audit-artifacts/2026-09-23/v8-reference-review/burnside-review.md)
- [可換群・純群のmodel completeness](audit-artifacts/2026-09-23/v8-reference-review/model-complete-review.md)
- [可解群・冪零群の既存結果](audit-artifacts/2026-09-23/v8-reference-review/nilpotent-review.md)
- [Chang–Keislerの引用番号](audit-artifacts/2026-09-23/v8-reference-review/chang-keisler-review.md)
- [Takeuchi2022原文](https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/2218-10.pdf)
- [HKTY v2, Thm.3.3](https://arxiv.org/html/2312.08988v2#S3.Thmtheorem3)
- [FK v2, Thm.3.6](https://arxiv.org/html/2512.09414v2#S3.Thmtheorem6)
- [dEMRS v3](https://arxiv.org/abs/2310.17595v3)
- [Saracino1976原著abstract](https://link.springer.com/article/10.1007/BF02757003)

ローカル監査ディレクトリには取得した一次PDF、必要な頁画像、
公開抜粋、書誌データを保存した。追加原文を得たら、
同じv8のhashと行位置に対して、保留箇所の判定を更新できる。
