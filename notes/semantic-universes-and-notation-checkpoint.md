# 任意宇宙の意味論と群の記法

2026-09-10。Notation 2.1、Definitions 2.2/2.4、Facts 2.3/2.5、および e.c. 群の結果の
一般宇宙への接続を対象とする。102モジュールの全体検査が警告0で通過した。

## 固定した検証結果

`python3 scripts/check.py` の全6段階が終了コード0、入力不変で通過した。
保存時にも全入力の SHA256 が live と一致した。2,768宣言のうち private-name 522、
public-name 2,246で後者は全て exported。exported 2,262には生成された private-name の
補題16個も含む。許可および実際の公理は `propext`、`Classical.choice`、`Quot.sound` のみ。
50項目・75部分項目の対応表は49 proved・0 partial・1 planned。
[全入力・宣言・ログ](audit-artifacts/2026-09-10/semantic-universes-notation/README.md) を固定した。
pin 済みキャッシュを使用するローカル検証であり、mathlib 自体の clean build や CI ではない。

## 数学的な変更

`GeneratorRank/Cardinal.lean` は任意群の最小生成基数 `Group.cardinalRank` を定義する。
実際の生成集合がその最小値を達成し、有限基数となることと有限生成性は同値である。
有限生成群では mathlib の `Group.rank` と一致するので、本文の全数値評価と接続する。
`Notation.lean` は native 交換子・右共役の式、通常の自由積の一意な lift、normal closure
の最小性を登録する。これで Notation 2.1 の全記法を覆う。

`LocallyFinite/Universes.lean` と `UniformLocalFiniteness/Universes.lean` は有限集合を含む
小さい初等部分構造を用い、局所有限性、有限 QF 図式、compactness で得た同じ有限型 cover
と位数の一様上界を任意宇宙のモデルへ移す。`Small` や有限部分構造の T-model 性を
新たな仮定にはしない。空の有限集合も含む。

`ElementaryReflection.lean` は、モデル完全な理論のモデルへの embedding が存在式を
反映すれば初等的であることを独立な2宇宙で証明する。入力モデルの T-model 性を
要求しない。既存の QF existential neighborhood と Tarski–Vaught の証明を再利用する。

`ExistentialClosedness.lean` の `IsExistentiallyClosedAt` はモデルと同じ宇宙を扱う
e.c. の一般形である。canonical universe では既存の e.c. 定義と定義的に一致する。
全入力モデルの像を含む Skolem hull の構成により、任意宇宙の拡大から存在式を反映する。
Π₂ 理論の model companion のモデルと、この一般 e.c. class が全宇宙で一致する。
有限パラメータを固定する実際の embedding transfer も一般化した。

この transfer により `ExistentiallyClosedGroups`、`StrictEnvelope`、`Main/BoundedWitness`
の既存定理のモデル宇宙を一般化した。元の root 構成、support、二段階 strictification、
有限図式、両側の非 amalgamation 証人の証明は保ち、`15n²` と
`15((3m+4)t(m)+1)²` を変更していない。canonical の既存 caller も型変換だけで通る。

新しい記法と一般意味論、有限図式、主定理への接続をソース・型・証明で独立に照合した。
原稿 SHA256 は `79745dfa1660a827c51ec3c6b2006ee9d6243cb4702f97a75e5b55357b89f50b`。
数学ソース revision は `a7c4521c9a402b1b112ae00824f55b728bf1dcdbd405d92c384c63c688ed0d49`。

## 残る境界

Remark 4.10 の共有根構成と、一般 Fact 2.6 における任意宇宙の ordinary amalgamation
の判定が残る。群論の amalgam は既に任意宇宙を扱い、主定理自体は一般化済み。
論文全体の goal は継続する。過去の検証成果物は固定したまま保持する。
