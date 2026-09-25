# v8 文献再監査: Eklof–Fischer / Eklof–Sabbagh

> 後続更新（同日、Eklof単著の全文到着後）：以下は到着前の判定記録である。Eklof–Fischerへの直接帰属に不一致という点は維持するが、単著のTheorems 4 and 7を組み合わせるとinductive＋JEP版を導けることを確認した。本文をcomplete theoriesに狭めることは必須ではない。現在の結論と追加論証は [Eklof単著の全文監査](eklof-1972-fulltext-review.md) を参照。

日付: 2026-09-24。追加された出版社PDFを独立に再照合した。TeX、Lean、前日の監査メモは変更していない。

## 結論

1. **v8:133 の Eklof–Fischer への帰属は、その原著に記された結果と一致しない。** 「inductive かつ JEP をもつ任意のアーベル群の理論には model companion がある」という定理は明示されておらず、最も関連する結果を実際に読むと、そのまま適用できる系でもない。したがって引用の修正、または別の根拠・独立の証明が必要である。
2. **これは、その一般命題が偽であるとの判定ではない。** 本監査は反例を与えておらず、EFの分類理論を利用した別の論証が不可能であるとも主張しない。「当該原著への直接帰属を確認できない」と「数学的偽」を区別する。
3. **v8:1502 の Eklof–Sabbagh 引用は原著 Theorem 2.4 と一致する。** ただし現在は `\if0` 内の非表示本文。全アーベル群の理論には、model companion より強く model completion がある。
4. **v8:136 の全群の非存在結果は ES Theorem 7.17 とも一致する。** v8 はそこで Chang–Keisler を引用しているが、ESを一次文献として追加するなら正しい参照になる。

## EF1972: 語句検索以外に確認した内容

原著: P. C. Eklof and E. R. Fischer, *The elementary theory of abelian groups*, Annals of Mathematical Logic 4 (1972), 115–171, DOI: <https://doi.org/10.1016/0003-4843(72)90013-7>。

使用PDF: `references/publications/eklof-fischer-1972-elementary-theory-of-abelian-groups-published.pdf`。印刷頁はPDF頁に114を加えたもの。

| 原著箇所 | 内容 | v8:133 との関係 |
| --- | --- | --- |
| Introduction, pp.115–116 | 飽和アーベル群の構造からSzmielew不変量、初等同値、決定可能性、飽和モデルの存在、拡大言語での量化子消去、Dedekind整域上の加群へ進む構成 | model companion の一般存在定理を成果として掲げていない |
| Theorem 2.4 / Corollary 2.5, p.140 | AがBのpure subgroupで、両者のelementary invariantsが同じなら A≺B。特にpureかつ初等同値なら初等部分構造 | purityと同一不変量が明示的な追加前提。JEPだけからこれを任意の二モデルに適用できない |
| Theorem 2.6, p.140 | 同じelementary invariantsをもつアーベル群は初等同値 | 既に不変量の一致が必要。e.c.モデルが一律の不変量をもつことをここでは証明していない |
| Theorem 2.8, p.141 | complete extensionsをcore sentencesで公理化でき、consistentな一文は有限個のcore sentencesから導ける | 完全理論の分類。任意のinductive Tに対するe.c.クラスの公理化定理ではない |
| Theorems 4.8–4.10 / Corollary 4.11, pp.158–160 | core sentencesに対応する命題定数と、可除性を表す関係記号を追加した言語でQE。元言語ではcore sentencesと可除性・非可除性条件の組合せへの還元 | 元の純群言語で任意の埋込みが初等的になるとの結論ではない |
| Theorem 5.5, p.168 | 上記の拡大言語QEをDedekind整域上の加群へ一般化 | 同じ言語・埋込みの相違が残る |
| Added in proof, p.170 | Kargapolov / Kozlov–KokorinのSzmielew理論の証明とRobinson testについての注意 | v8:133の定理の追記ではない |

Introduction、p.140、pp.158–159はページ画像でも確認した。既存の抽出テキストにはOCR誤りがあるが、この判定を左右する前提・結論は画像上で確認できる。全体の定理配置と上記の数学的内容を確認したので、単なる「model companionという語が検索されない」ことだけを根拠にしていない。

### なぜ単純な言換えや直接の系にはできないか

EF Corollary 2.5は、**同じ完全理論内のpure embedding**を扱う。一方、v8は**必ずしも完全でないinductive理論Tの全モデル**から出発し、そのmodel companionの存在を結論する。通常のJEPは二モデルを共通モデルへ埋め込めるという条件であり、初等同値やcore sentencesの真理値一致そのものではない。

また、EF Theorem 4.10の定義的拡大がQEをもつことから、元言語の任意の埋込みが初等的であるとはいえない。例えば群の埋込み `Z -> Q` は元の群演算を保つが、`2 | 1` の真理値を保たない。可除性関係を追加した拡大構造の埋込みにはならない。この点を省いて元言語のmodel completenessを結論することはできない。

v8の一般命題をEF経由で証明するなら、少なくとも次の追加論証が要る。

- 任意の対象理論Tに対し、候補となる一階理論T*を構成すること。
- Tの全モデルがT*のモデルへ埋め込まれ、T*がTの要求を保つこと。
- T*間の埋込みにEFのpurity・同一不変量条件を適用できること。

e.c.モデルを取れば、そのT拡大への埋込みのpurityは得られる。しかし、**e.c.クラスの一階公理化可能性**またはそれに代わるT*の構成は、それだけでは解決しない。ES Corollary 7.13（p.288）がまさにこの公理化可能性をmodel companion存在の条件にしている。今回読んだEFの結果にはこの橋渡しは含まれていない。よって、「EFが証明した」と断言する現在の記述は採用できないが、一般命題の真偽は本監査の判定外とする。

## Eklof 単著 JSL37(1972) との差

出版社の一次抄録を再確認した文献:

P. C. Eklof, *Some model theory of abelian groups*, Journal of Symbolic Logic 37 (1972), no.2, 335–342, DOI: <https://doi.org/10.2307/2272976>。

公式ページ: <https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/some-model-theory-of-abelian-groups/723738E35EF8C76F5D17F141746CE62B>。

そこで明示される結果は「**complete inductive** theories of abelian groups が、ちょうどmodel-complete theoriesである」というもの。著者はEklof一人で、EF1972とは別論文である。

完全性の仮定があるため、これを「incompleteでもよいinductive+JEP理論はmodel companionをもつ」に置き換えることはできない。後者から前者が従う方向は説明できるが、逆向きには上記の存在・公理化の論証が別途必要である。単著論文に差し替えるなら、本文の主張もcomplete理論についての正しいものに変更する必要がある。

この単著論文は公式抄録を確認した範囲であり、全文の定理番号まで確認したとはしない。公式PDFリンクへの取得はPDFでなくHTMLを返した。したがって、修正案のlocatorは当面論文全体または抄録の内容に限る。

## ES1971: 一致する具体的結果

原著: P. Eklof and G. Sabbagh, *Model-completions and modules*, Annals of Mathematical Logic 2 (1971), no.3, 251–295, DOI: <https://doi.org/10.1016/0003-4843(71)90016-7>。

使用PDF: `references/publications/eklof-sabbagh-1971-model-completions-and-modules-published.pdf`。印刷頁はPDF頁に250を加えたもの。

### Theorem 2.4, p.256: 全アーベル群

pp.255–256でKを全アーベル群の理論とし、K*のモデルは、可除で、各素数pについて位数pの元を無限個もつアーベル群と定義する。Theorem 2.4はK*がKのmodel companionであり、APによりmodel completionでもあると結論する。純群言語とZ加群言語の両方で成立する旨がp.255に明記されている。

したがってv8:1502の存在主張は一致する。なお「可除アーベル群である」だけでは不足し、各素数位数の元の無限性も必要である（原著p.290でもQがe.c.でないことを注意している）。v8は候補の誤った公理を述べていないので問題ない。

### Theorem 7.17, p.291: 全群

全群の理論にmodel companionが存在しない、と明示する。直後の証明では積・逆元・単位元の通常の群言語を採用し、e.c.群のクラスがultraproductで閉じないことからCorollary 7.13を用いる。v8:136の主張と同じ。

Theorem 2.4 と7.17はいずれも供給されたページ画像で確認した。現行v8のES引用は非表示部分だけにあるため、活動本文にESの引用を追加するなら、上記二箇所が適切な引用先になる。

## 修正方針の提案（実施していない）

- 安全な最小修正: v8:133の一般論は、別証明・正確な引用が確保されるまで削除し、全アーベル群の例にES Theorem 2.4を付す。
- または、Eklof単著の「completeならinductiveとmodel completeが同値」という別の正確な結果へ、本文と文献を合わせて変更する。
- 現在のinductive+JEP命題を保持する場合は、直接の出典、または上記の橋渡しを含む証明を追加する。書誌名だけの置換では解決しない。

これは証明済みの誤帰属への対応案であって、命題自体を偽と断定して削除を勧めるものではない。
