# v8 参考文献再レビュー（2026-09-24）

後続の記録: 同日に論文全体をあらためてレビューした [v8 論文の再レビュー](v8-paper-review-2026-09-24.md) がある。
183行の帰属（Novikov–Adian／Adian）、201行の論理の向き、151行の先行研究（Burris–Werner、
arXiv:2609.05789）、144行の Maier の直接帰属、EF の共著者名の表記（Fisher）は、そちらで追加・更新した。

更新：同日追加された `references/saracino1976.pdf` と `references/on-the-burnside-problem-on-periodic-groups-5fnzsr8mqf.pdf` も照合済み。Saracino 1976の全文確認とIvanov 1992の出版版確認の保留を解消した。原本は提供された場所に保持し、資料台帳・不足一覧を更新した。

追加更新：`references/2272976.pdf`（Eklof単著）も全文照合した。**133行の一般命題は同論文のTheorems 4 and 7から導ける**ことを、下記の追加論証で確認した。現行のEklof–Fischerへの直接帰属は修正が必要だが、数学的主張をcomplete theoriesの場合に狭める必要はない。単著論文も不足一覧から除いた。

追加された出版版PDFを原文と照合した結果、**Eklof–Fischerへの帰属は修正が必要**であり、**Ivanovの引用には階数条件の明記が必要**である。Saracino 1974、Saracino–Wood 1979、Maier 1989、Eklof–Sabbagh 1971の保留は、今回の原著確認で解消した。

対象は [T3_modelcompanion_v8.tex](/home/ywr/t3-model-companion/T3_modelcompanion_v8.tex)。SHA-256は `9546045ccd5cb0170ac54fe1485d356765400ed938c57442da558c41c51fa38c`。以下の行番号はこのファイルに対応する。原稿・Leanは変更していない。

参考文献は13件、表示本文で引用される文献は12件。Eklof–Sabbaghの引用は現在 `\if0` 内にある。今回追加分は独立に再読し、既確認分は同一の原稿・資料ハッシュに対応する前回の照合記録を引き継いだ。全参考文献の証明を再証明したという判定ではなく、原稿が引用する主張の仮定・結論・量化範囲・言語・参照箇所の監査である。

## 修正が必要な箇所

### 1. Eklof–Fischerへの帰属（133行）

原稿は「inductiveでJEPをもつ任意のアーベル群の理論にはmodel companionがある」とEklof–Fischerに帰属している。

追加された *The elementary theory of abelian groups* 全文を確認したが、この一般存在定理は原著に述べられていない。関連する原著の結果は以下である。

- Theorem 2.4 / Corollary 2.5、p.140：pure subgroupかつ同一のelementary invariants／初等同値という条件の下で初等部分構造となる。
- Theorem 2.8、p.141：complete theoriesをcore sentencesで記述する。
- Theorem 4.10 / Corollary 4.11、pp.158–160：可除性などを追加した言語での量化子消去と、元の言語での式の還元。

これらから原稿の結論へ進むには、任意の対象理論のe.c.モデルのクラスが一階公理化できることなど、追加の論証が必要である。JEPは初等同値を意味せず、拡大言語の量化子消去も元の群言語のmodel completenessをそのまま意味しない。

**現在の判定：出典と帰属表現を修正すれば、一般命題は保持できる。** 以下のEklof単著の結果と追加論証によって、前回未確認だった橋渡しを確認した。

Eklof単著 *Some model theory of abelian groups*, JSL 37 (1972), 335–342 は、今回の `2272976.pdf` で全文を入手した。**Theorem 7(a),(d)、pp.339–340** は、アーベル群Aの完全理論Th(A)についてinductiveであることとmodel completeであることの同値を述べる。Theorem 7単独の文言は、v8のinductive＋JEP命題とは異なる。

ただし、同論文の **Theorem 4、p.336**（普遍理論の特徴づけ）と、**Theorem 7(b),(d)**（model completenessの代数的判定）を組み合わせると、原命題を次のように導ける。

1. JEPとコンパクト性から、Tと整合的な全存在文を満たすAをTのモデルとして選べる。このとき `Th(A)_forall = T_forall`。
2. 各素数pについて `dim((p^n A)[p])` の列（有限次元はその値、無限次元は∞）を保ち、有限指数か否かも保つ群Cを、有限巡回群・Prüfer群・必要に応じQの直和で構成する。
3. Cの各p成分を、Theorem 7(b)の条件を満たすように選べる。具体的には上の列が初めて有限になる位置を唯一の無限重複度の巡回成分とし、それ以降の有限差分と最終定数値を有限巡回成分・Prüfer成分で実現する。全項が∞なら可算個のPrüfer群で実現する。
4. Theorem 4によりCとAは普遍同値、Theorem 7によりTh(C)はmodel complete。従ってTh(C)はTと同じ普遍的帰結をもつmodel-complete theoryで、v8の定義におけるmodel companionとなる。

完全な構成と各条件の確認は[Eklof単著の全文監査・導出証明](/home/ywr/t3-model-companion/notes/audit-artifacts/2026-09-24/v8-reference-review/eklof-1972-fulltext-review.md)に記録した。これは**今回、原著の結果から導いた系**であり、原著のTheorem 7にJEP版がそのまま印刷されているという意味ではない。

修正案（未実施）：

```tex
More generally, it follows from Eklof's results that every inductive
theory of abelian groups with the joint embedding property has a model
companion~\cite[Theorems~4 and~7]{Eklof1972}.
```

この文に対応するEklof単著の書誌を追加し、上の導出を短い補足として添えれば、主張を狭めずに根拠を明確にできる。前回提案した一般文の暫定削除・complete theoriesへの変更は、もはや必須ではない。旧評価の経緯は[アーベル群文献の先行監査](/home/ywr/t3-model-companion/notes/audit-artifacts/2026-09-24/v8-reference-review/abelian-review.md)に保持する。

### 2. Ivanovの階数条件（183行）

IvanovのTheorem A(a)は `m > 1`、`n >= 2^48` の下で自由Burnside群 `B(m,n)` が無限と述べる。今回提供された出版版の **p.258** でも同じ条件・結論を確認した。原稿の「十分大きな素数に対して自由Burnside群は無限」には **rank at least two** を補う必要がある。階数1では `B(1,p) = C_p` は有限である。

修正案：

```tex
The free Burnside groups of rank at least two are infinite for such
primes \cite[Theorem~A]{Ivanov1992}, ...
```

非局所有限性についての意図した議論には階数2で十分なので、この補足でその論点は保たれる。なお182行で予告する別稿の非存在証明は、この参考文献監査の検証対象に含めていない。

出版版の確認記録：[Ivanov 1992](/home/ywr/t3-model-companion/notes/audit-artifacts/2026-09-24/v8-reference-review/ivanov-published-review.md)。1992年の論文は結果と証明の概説を載せる短報であり、その全文所蔵とBurnside定理の詳細な全証明の監査は区別する。

## 追加資料によって確認できたこと

| 文献 | 原著箇所 | v8との照合結果 |
|---|---|---|
| Saracino 1974 | Theorem 1、p.327。定義pp.327–329 | 各 `n >= 2` について可解長 **at most n** の群の理論にmodel companionはない。138行の意図と一致。上界を明記する表現への精密化を推奨。 |
| Saracino 1976 | Theorem 1、p.241、Theorem 2、p.242。証明pp.243–245 | 各 `n >= 2` についてclass at most nの一般・torsion-freeの両理論にmodel companionはない。139行と一致し、従来の抄録のみの確認から全文確認へ更新。 |
| Saracino–Wood 1979 | Theorem 3.9、p.198。定義p.189、証明pp.198–200 | 任意の `2 <= m < infinity`、恒等式 `x^m=1`、class at most 2、通常の群言語でmodel companionが存在する。偶数指数も含み、102–103・143行と一致。 |
| Maier 1989 | Theorem 3.5、p.285、証明p.286。クラスの定義p.279 | `p` 素数、`c < p`、`K = N_c ∩ B^p` のmodel companionの存在を**直接**証明する。103–104・144行と一致。 |
| Eklof–Sabbagh 1971 | Theorem 2.4、p.256 | 全アーベル群のmodel completionが存在。1502行の非表示引用と一致し、132行の最初の例にも適切な出典となる。 |
| Eklof–Sabbagh 1971 | Theorem 7.17、p.291 | 全群の理論にmodel companionはない。136行でChang–Keislerを介して引用している結果の一次出典として使える。 |

SWの抽出テキストはTheorem 3.9の下限を `2 < m` と誤読しているが、原頁画像は **`2 <= m`** である。Maierの証明にはcoupled central seriesやamalgamation basesが現れるが、これらを対象群全体への追加仮定と解釈してはいけない。Theorem 3.5のmodel companionは拡大言語ではなく群言語であり、p.286の公理でも確認した。

引用位置はそれぞれ `\cite[Theorem~3.9]{SaracinoWood1979}`、`\cite[Theorem~3.5]{Maier1989}` と特定できる。Maierの原著で直接の根拠が確保されたので、この存在主張の照合はdEMRS出版版の入手待ちではない。

Saracino 1974について、現行の「fixed derived length at least 2」を厳密にexactly nと読む場合も、可解長nの群との直積への埋込みを使えば対応する非存在結果が従う。このため誤った数学的主張とは判定せず、原著と同じ上界表現への改善とする。

詳細：[冪零群文献の独立監査](/home/ywr/t3-model-companion/notes/audit-artifacts/2026-09-24/v8-reference-review/nilpotent-review.md)、[可解群文献・所蔵一覧の独立監査](/home/ywr/t3-model-companion/notes/audit-artifacts/2026-09-24/v8-reference-review/solvable-review.md)。

Saracino 1976の追加確認：[全文監査](/home/ywr/t3-model-companion/notes/audit-artifacts/2026-09-24/v8-reference-review/saracino-1976-fulltext-review.md)。通常の群言語、classの上界、torsion-freeの場合の証明の修正を原頁で確認した。引用は `\cite[Theorems~1 and~2]{Saracino1976}` と精密化できる。交換子規約はv8と異なるが、引用されているclassの上界と非存在結果には影響しない。

## 全13文献の現在の状態

「全文あり」は当該版の資料がローカルにあるという意味であり、文献の全証明を検証済みという意味ではない。

| 文献 | 手元の資料 | 数学的照合・残る境界 |
|---|---|---|
| Chang–Keisler 1990 | 出版本文の公開抜粋 | Example 3.5.16、p.199の全群の非存在主張は一致。書籍全文はないが、証明の一次出典ES1971は今回入手済み。 |
| d’Elbée–Müller–Ramsey–Siniora 2025 | arXiv v3全文 | Corollary 4.42、pp.33–34で群言語の結果を確認済み。奇素数 `p > c` の範囲。`p=2, c=1` は別途アーベル群のケース。出版版の定理番号・掲載位置は未確認。 |
| Eklof–Fischer 1972 | 出版版全文 | **133行の直接帰属に不一致。** 命題自体は別論文のEklof単著Theorems 4 and 7から導出できる。上記参照。 |
| Eklof–Sabbagh 1971 | 出版版全文 | Theorems 2.4 / 7.17と一致。現状の引用は非表示部分のみなので、表示本文に適切な引用を置くとよい。 |
| Frącek–Kowalski 2025 | arXiv v2全文 | Theorem 3.6、p.10。任意の体KについてH(K)のmodel completenessとKのmodel completenessが同値。147行の一方向の主張と一致。標数の追加条件なし。 |
| Hoffmann–Kowalski–Tran–Ye 2023 | arXiv v2全文 | Theorem 3.3、p.18。model-complete field上のsplit semisimple groupの有理点群等について、純群としてmodel complete。147行の「some」と一致。 |
| Ivanov 1992 | 出版版全文（旧著者版も保存） | Theorem A(a)、出版版p.258。旧著者版と同じ条件・結論を確認。**階数条件の補足が必要。** |
| Levi–van der Waerden 1933 | 出版版全文 | Satz 1、pp.156–157。位数 `3^(C(r,1)+C(r,2)+C(r,3))` と一意正規形。交換子の規約も一致。167・609行を支持。 |
| Maier 1989 | 出版版全文 | Theorem 3.5、pp.285–286で直接一致。 |
| Saracino 1974 | 出版版全文 | Theorem 1、p.327で一致。可解長の上界を明記する改善。 |
| Saracino 1976 | 出版版全文 | Theorem 1、p.241、Theorem 2、p.242。class at most c、`c >= 2` の一般・torsion-freeの両非存在が139行と一致。証明の対象範囲もpp.243–245で確認。 |
| Saracino–Wood 1979 | 出版版全文 | Theorem 3.9、p.198で直接一致。 |
| Takeuchi 2022 | 出版版全文 | Theorem 17、PDF p.5がtorsion-free群の非存在を支持。PDF p.2はBurnside問題との関連を指摘しており172行と一致。v8の具体的iff予想がこの既刊論文に載るという帰属ではない。 |

合計は出版版全文9件、著者版／preprint全文のみ3件、公開抜粋のみ1件（CK）。PDFの実在、ページ数、SHA-256は今回再確認し、[資料台帳](/home/ywr/t3-model-companion/notes/audit-artifacts/2026-09-24/v8-reference-review/source-inventory.json)に保存した。書誌年がpreprint初版の年でも、ここに記した定理番号は所蔵するv2の番号である。

この13件とは別に、引用修正候補のEklof単著1972も出版版全文を所蔵し、Theorems 4 and 7を確認済み。

## まだ不足している資料

### 現行v8の文献で、優先して入手したいもの

| 文献 | 入手したい版・範囲 | 残っている確認 |
|---|---|---|
| **C. d’Elbée, I. Müller, N. Ramsey, D. Siniora, Model-theoretic properties of nilpotent groups and Lie algebras**, J. Algebra 662 (2025), 640–701 | **出版版**全文。[DOI](https://doi.org/10.1016/j.jalgebra.2024.08.012) | 著者版v3は所蔵・照合済み。v8が指定するCorollary 4.42の番号を出版版と照合する。 |

dEMRSの[所属機関の書誌ページ](https://fount.aucegypt.edu/faculty_journal_articles/6073/)は同日の先行レビューで読めたが、そのDownload先は403で本文を取得できなかった。その後の提供資料にも含まれないため、この保留は残る。

### 出版版の保存を揃える目的なら追加できるもの（優先度低）

- **C. C. Chang and H. J. Keisler, Model Theory**, third edition, North-Holland, 1990。必要箇所は **Example 3.5.16、pp.199–200**。p.199の公開抜粋と一次出典ES1971があるため、書籍全体の取得は今回の確認の必須条件ではない。

前回不足していたEklof–Fischer、Eklof–Sabbagh、Saracino 1974、Saracino–Wood、Maierに加え、Saracino 1976、Ivanov 1992、修正候補のEklof単著1972の出版版も入手済みであり、再取得は不要。HKTYとFKはv8自体がpreprintを引用しており、所蔵版全文で照合済みなので不足リストには含めない。

## 監査の境界

- 今回の保存・更新物は本ノート、個別監査ノート、抽出テキスト、必要な原頁画像、資料台帳（references/MANIFEST.mdを含む）のみ。原PDFは保持し、原稿・Leanは編集していない。
- 未入手の全文を確認済みとはしていない。出版版の定理番号と著者版の番号も区別した。
- 原稿の独自の主定理・別稿の予告・先行研究全体に関する網羅的な新規性判断は、この引用照合だけでは検証されない。
- TeXのコンパイルやLeanビルドは本レビューでは実施していない。
