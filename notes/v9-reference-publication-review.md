# v9 序論・参考文献・公開用メタデータのレビュー

確認日: 2026-09-25。

対象は受領した v9 原稿と、`README.md`、`formalization.yaml`、`docs/palomar.md`、
`Challenge.lean`、`Solution.lean`、`comparator.json`。受領原稿の SHA-256 は
`d48f10716bcc7963b654c6fe27013ac75eaa9cbdf6593683a0efc513dd062952`。
以下の原稿行番号は、この**修正前の受領原稿**を指す。統合後の原稿の版・ハッシュ・検証は
[v9 移行記録](v9-migration.md) と区別する。

## 結論

v9 の Maier への直接帰属と Novikov–Adian／Adian への引用変更は適切である。
Novikov–Adian Part II の **241–479 頁は正しく、誤植ではない**。
残る必要な修正は、Eklof の原定理とその系の区別、可解長の上界の明示、
新規性の断定の範囲、および形式化の著者・対象範囲の明示である。
主定理の仮定や定数を変更する理由は、このレビューでは見つからなかった。

## 原典を再確認した変更箇所

| 受領 v9 | 確認した原典・箇所 | 判定 |
| --- | --- | --- |
| 133–135 行、Eklof1972 | 出版版 `references/2272976.pdf`、Theorem 4（p.336）、Theorem 7（pp.339–340）、既存の導出記録 | JEP 版は原著にそのまま書かれた定理ではなく、Theorems 4 and 7 からの系。数学的主張は維持して「これらから従う」と明記する。 |
| 147–149 行、Maier1989 | 出版版 `references/publications/maier-1989-nilpotent-groups-of-exponent-p-published.pdf`、Theorem 3.5（p.285） | `c < p` のクラスに対する ℵ₀-categorical model companion を直接述べている。v9 の変更は一致。定理番号を付ける。 |
| 189–192 行、NovikovAdian1968 | Part I 出版版 p.209 の Theorem | `m ≥ 2`、奇数 `n ≥ 4381` の無限 m 生成指数 n 群。受領 v9 は自由群の全階数についての主張をやめ、Burnside 問題の否定的解決を述べるので、旧版の階数の曖昧さは解消済み。 |
| 1565 行、Part II の頁 | Part II 出版版の最初と最後の頁（241、479）、Crossref 保存記録、Math-Net の現在の出版者記録 | 241–479 を保持する。全 239 頁の論文であり、241–279 等に訂正してはいけない。 |
| 191 行、奇数指数 665 | Springer の書誌情報と、Adian 自身の後年の説明 | 1979 年英訳書への引用と「奇数指数 ≥665」は適切。1979 年の書籍全体・全証明を今回読んだという判定ではない。 |

Eklof、Maier、Novikov–Adian I の上記の定理は保存済み原頁画像も再確認した。
Part II は保存済み出版版抽出テキストの開始頁・終了頁と出版社レコードを照合した。
旧資料の再ダウンロードはしていない。

今回開いた一次資料の公開入口:

- [Eklof 1972 の Cambridge 出版者ページ](https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/some-model-theory-of-abelian-groups/723738E35EF8C76F5D17F141746CE62B)：著者、年、巻号、頁、DOI、完全理論についての抄録を確認。
- [Novikov–Adian Part II の Math-Net 出版者ページ](https://www.mathnet.ru/eng/im2475)：英訳の巻号・241–479 頁・DOI を確認。
- [Adian の書籍の Springer ページ](https://link.springer.com/book/9783642669347)：1979 年、シリーズ第 95 巻、書名・著者を確認。2011 年は当該 paperback 再刊の発売日であり、引用年の置換には使わない。
- [Adian 自身の 2003 年講演概要](https://www.mathnet.ru/php/seminars.phtml?option_lang=eng&presentid=1244)：自身による 1975 年の改良を奇数 `n > 664` と明記。
- [Adian, The Burnside problem and related topics (2010)](https://www.mathnet.ru/php/getFT.phtml?jrnid=rm&paperid=9376&what=fullteng)：p.807、Theorem 2 と書籍への帰属を確認する補助資料。PDF の検索抽出では不等号が `>` に化けるため、境界値の判断はこの抽出だけに依存していない。

数学的引用範囲の追跡には [v8 参考文献レビュー](v8-reference-review-2026-09-24.md) と
[v8 論文レビュー](v8-paper-review-2026-09-24.md) を併用した。変更のない文献の全証明を
今回一から再監査したわけではない。d’Elbée ほか 2025 の Corollary 4.42 は保存済み
出版社配布著者原稿版で確認されているが、最終組版版の頁・番号の照合は未実施のままである。

## 原稿への必要な修正

### Eklof の帰属

原著の Theorem 7 は完全理論 `Th(A)` の帰納性とモデル完全性の同値を述べる。
Theorem 4 の普遍理論の特徴づけと組み合わせることで JEP 版が得られる。
その導出は [Eklof 単著の全文監査・導出](audit-artifacts/2026-09-24/v8-reference-review/eklof-1972-fulltext-review.md)
にあり、今回その群の構成・次元列・JEP によるコンパクト性の段階を再確認した。

最小の修正は、主張を狭めず次のようにすること。

```tex
More generally, it follows from Eklof's criteria for universal equivalence
and model completeness that every inductive theory of abelian groups
with the joint embedding property has a model companion
\cite[Theorems~4 and~7]{Eklof1972}.
```

これは原著に JEP 版が逐語的に印刷されているという帰属を避ける修正である。
新しい Lean 結果や未証明の公理を追加する必要はない。

### 可解群・先行研究の表現

- 141 行の `fixed derived length at least 2` は、各 `n ≥ 2` について
  `derived length at most n` と明記し、Saracino1974 の Theorem 1 を付ける。
  続く文の `solvability` も `a fixed bound on the derived length` とする。
- 156 行の `no general result is known` は、網羅的な文献調査なしの一般的断定であり、
  前回調査済みの Burris–Werner/Burris の一般存在定理との関係も不明確である。
  ここでは新しい先行研究の節を追加せず、直前に紹介した結果の範囲に限定して
  `These results do not provide a general criterion deciding which nonabelian
  group varieties have a model companion.` とする。
- 受領 v9 は参考文献 14 件のうち EklofSabbagh1971 だけを本文で引用していない。
  全アーベル群の存在には同論文 Theorem 2.4、全群の非存在には Theorem 7.17 を引用できる。
  いずれも旧レビューで出版版を確認済み。全アーベル群の引用を、torsion-free／固定指数の
  例の列挙から分ければ、Theorem 2.4 単独の直接の射程が明確になる。

### 形式化の著者・対象範囲

221 行の `We have also fully formalized all the results in this paper` は、
次の二点を明示する必要がある。

1. 形式化の著者・責任保守者は Yawara Ishida 一人であり、論文の三著者とは区別する。
2. 対象は §2–§5 の証明された数学的結果である。一般の Conjecture 1.1 と、
   別稿で証明を公表すると予告している十分大きい素数指数の結果は含めない。

`The first author has formalized ... the mathematical results proved in Sections ...`
と書き、上記の除外範囲を明記する。225 行の `GitHub soon` は期日を裏付けないため、
別リポジトリに準備され公開は別途告知されるという事実の範囲に留める。
新たな DOI、公開 URL、投稿、登録、査読通過を示す文は加えない。

## リポジトリの公開用記述

レビュー開始時の `README.md`、`formalization.yaml`、`docs/palomar.md` は、
既に著者三人と形式化著者一人、一般予想の未解決性、別稿予告の対象外、
局所的な検証と Palomar 投稿・登録の違いを正しく区別していた。
移行で必要なのは原稿名、原稿ハッシュ、現行ソース位置、現在の検証記録への参照、
および旧 §6 の説明の更新である。

受領 v9 は旧 §6 自体を削除している。したがって現行版について
`disabled former Section 6` や `v9 の if0 内` と書くのは不正確になる。
旧 v7 の質問二件と既知の Burnside／局所有限性の同値はアーカイブ由来として保持する。
これらを v9 本文の現役項目へ戻してはいけない。

`Challenge.lean` と `Solution.lean` の仕様対象は Theorem 3.3 と Corollary 3.4 の二つ。
`comparator.json` もその二宣言を選び、許可公理は `propext`、`Quot.sound`、
`Classical.choice` のままである。Challenge の二つの deliberate holes は仕様用であり、
数学ライブラリの証明完了数と混同しない。現行原稿への行番号の更新は必要だが、
序論の文献変更を理由に二つの仕様の仮定や結論を変更する必要はない。

Lean/mathlib の固定版は現地ファイルで確認した v4.34.0 と
`5ed2965256430c3649e86755f9576b54eca72435`。今回の文献担当は依存関係を更新せず、
ビルドや Comparator を実行していない。それらの成否は移行担当の検証記録に従う。
GitHub の非公開性や Palomar のポリシーについて既存の 2026-09-22 の記録は
**その日の確認**として保持し、今回再確認した事実へと書き換えない。

## 検証の境界

- 新規または変更された序論の引用、版間で残っていた帰属問題、公開用の数学的主張の範囲をレビューした。
- Conjecture 1.1 全般、十分大きい素数指数についての別稿の証明、引用文献の全証明の正しさを新たに証明したわけではない。
- 新規性についての網羅的な調査、リポジトリの公開、投稿、Palomar 登録、独立した人間の査読は行っていない。
- このノートの変更提案と、実際に統合された原稿差分・Lean 検証・PDF 品質確認はそれぞれ別の記録である。
