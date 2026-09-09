# Associated graded の例と任意宇宙のモデル埋込み

2026-09-10。Example 2.21 と Definition 2.2(1) の宇宙移行を対象とする。
96モジュールの全体検査が終了コード0・警告0で通過した。

## 固定した検証結果

`python3 scripts/check.py` の全6段階が通過し、入力不変性と保存時の live SHA256 一致を
確認した。監査対象は2,734宣言、private-name 514、public-name 2,220で後者は全て
exported。exported 全体2,236には private-name の生成補題16個も含まれる。
許可および実際の公理は `propext`、`Classical.choice`、`Quot.sound` のみ。
50項目・75部分項目の対応表は48 proved・1 partial・1 planned。この個数は完成率ではない。
全入力・全宣言・6段階のログを
[保存成果物](audit-artifacts/2026-09-10/examples-model-embeddings/README.md) に固定した。
pin 済みキャッシュを使うローカル検証であり、mathlib の clean build や CI ではない。

## 論文との対応

`T3/GroupTheory/AssociatedGradedExamples.lean` は Example 2.21(1,3) を実装する。
可換群では第一層の代表元をそのまま元へ送る写像から、全 associated graded と元の群の
実際の Lie 同型を構成した。他の次数は零で、準同型に関する自然性も保つ。
指数3の仮定は体作用と Lie 代数の構成に使用し、有限性や非自明性を要求しない。

自由2生成群では、第二中心項が `[x,y]` の3つの冪そのものであり、第三中心項が自明である
ことを証明した。実際の商における `x̄`、`ȳ`、`[x,y]` が指定された基底である。
全 graded 空間の座標同型は括弧を行列式 `ab' - ba'` へ送り、次数1と2の部分空間を正確に
特定する。既存の直積の全次数公式と合わせ、Example 2.21 の全項目を覆う。

`T3/ModelTheory/ModelEmbeddings.lean` は、canonical universe で定義した
`ModelsEmbedInto` から、任意宇宙の非空モデルの埋込みを得る。
有限パラメータは小さい初等 Skolem hull に含まれ、そこへ元の埋込み条件を適用する。
QF diagram の有限部分を同時実現し、compactness からモデル全体の埋込みを構成する。
対象モデルの宇宙は言語と入力モデルの宇宙の最大値であり、入力モデルの `Small` や
理論の有限性・普遍性・完全性を仮定しない。Definition 2.2(1) の双方へ適用できる。

ソース、公開型、証明経路を読み合わせた。Examples は独立した数学レビューも通過した。
原稿 SHA256 は `79745dfa1660a827c51ec3c6b2006ee9d6243cb4702f97a75e5b55357b89f50b`。
数学ソース revision は `4361f8312b86001a2ef7f9d59326d9165f8afa6e2e6f2aae37ff9169b2a2817d`。

## 残る境界

主定理と model companion の存在は前の検証境界で証明済み。
今回の埋込み bridge だけでは、一般宇宙での e.c. の定義、局所有限性、一般 criterion、
e.c. を使う群論の結論までの接続を完了したことにはならない。
Notation 2.1 の一般生成基数等の登録と Remark 4.10 の共有根構成も残る。
論文全体の goal は継続する。過去の固定成果物は変更しない。
