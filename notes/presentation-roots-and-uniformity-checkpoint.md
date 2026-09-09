# 自由表示・同時根・一様局所有限性

2026-09-10。対象は v4 TeX、SHA256
`79745dfa1660a827c51ec3c6b2006ee9d6243cb4702f97a75e5b55357b89f50b`。
[前回の外積同型・quotientの境界](exterior-quotient-diagram-checkpoint.md) からの進展を記録する。
長期goalは論文全体のpaper-faithfulな形式化であり、未完了のまま継続している。

## 指定した基底と代表元からの自由表示

`GroupTheory/Generation.lean` は原稿の二段階の包含
`γ₂(G) ≤ H ⊔ [H,γ₂(G)] ≤ H ⊔ γ₃(G)` と `[H,γ₂(G)] ≤ H` を個別に証明する。
これにより `H ⊔ γ₂(G) = G` から `H = G` を得る。
旧 `Generation.lean`、`Nilpotent.lean` の分解・交換子恒等式を再利用し、
v4の包含の順序を明示した。associated gradedのLie生成性だけでは済ませていない。

`Presentation.lean` は任意の指定済み `Basis I (ZMod 3) (Layer G 1)` と、
その任意の指定代表元 `a : I → G` を引数に取る。
`Free.presentation_of_basis` は、その `Free.lift` が全射であり、核が自由群の
導来群に含まれることを証明する。実際の次数1の誘導写像も `LinearEquiv` にした。
`I` に有限性・可算性・順序の仮定はなく、証明内で一時的に順序を選ぶ。
旧 `Presentation.lean` の証明を再利用し、存在packageだけでなく指定データを保つ形にした。
これで Proposition 4.1 が完成した。

## 非斉次な関係式を保った normal closure

`GradedNormalClosure.lean` は任意の群Gと `K ≤ γ₂(G)` について、
原稿の `L = K[K,G]` と `L ≤ γ₂(G)`、次数2・3の像の公式を証明する。
群としての等式は旧 `NormalClosure.lean` を再利用し、実際の積 `k * p` の表示も公開した。

次数3では最初に `L ∩ γ₃(G) = (K ∩ γ₃(G))[K,G]` を証明し、それから像を取る。
`K` を次数ごとの成分に分離する仮定は使わない。
bracket部分空間は双線形写像の値のspanを表す標準 `Submodule.map₂` であり、
自由群の座標空間に限定していない。Kの正規性・有限性・Gの自由性も仮定しない。
これで Lemma 4.2 の全3項が完成した。
実装担当とは別の担当者も、非斉次relationとambient filtrationの扱いを原稿と照合した。

## 原稿の一括商による同時 triple roots

`Roots/Triple.lean` は任意の中心元の族 `g : Fin n → G` に対し、
`G × Free (Fin (3*n))` を関係式 `((g i)⁻¹, [xᵢ,yᵢ,zᵢ])` のnormal closureで割る。
原稿の符号・生成元数・一括商を保ち、単一rootの反復構成に置き換えていない。

旧 `CentralProduct.lean` の構成を再利用する。関係式の中心性からnormal closureを
生成部分群と同一視し、その有限積表示の各整数指数を独立な三重座標で回収する。
自由因子の成分が1なら全指数が3の倍数になるため、元の群との交叉は自明である。
`baseMap_injective` と各 `baseMap_root` の等式を証明し、Lemma 4.8 が完成した。
空族・自明群・重複または自明な中心元を含む。

## Block quotientと外積分解

`LinearAlgebra/BlockDecomposition.lean` はmathlibの `DirectSum.Decomposition` と
homogeneous predicateを用い、原稿の `W = ⨁ (W ∩ Bᵢ)` と同値であることを
iSup等式と独立性で証明する。`quotientEquiv` は各成分を交差部分空間で割る
具体的な写像から得られ、原稿の代表元公式と単一成分の逆像公式を持つ。
各成分商と全体商内の像との同型も公開した。任意の環・任意のindexで成立するため、
原稿の任意次元のvector spaceを含む。Definition 2.10・Proposition 2.11が完成した。

`LinearAlgebra/ExteriorSum.lean` は旧 `ExteriorSupport.lean` の射影を再利用する。
和集合に添字を持つ外冪基底を左側indexの数で分け、射影の和・冪等性・直交性から
実際の `DirectSum.Decomposition` を任意次数で構成した。
基底の大きさを有限と仮定しない。
これは Proposition 4.3 の証明準備であり、混合blockとtensorの同型をまだ与えていない。
η₁–η₃・自然性・block間bracketは未実装なので、同命題の状態は `planned` を維持する。

## 一様局所有限性と有限個のT同値類

`ModelTheory/UniformLocalFiniteness.lean` は、有限生成部分構造のQF図式から出発する。
全てのtupleの図式の否定を加えた理論が矛盾するため、compactnessにより有限個の
図式が全モデルの全n-tupleを覆う。この有限被覆の代表tupleが生成する部分構造の
濃度の最大値を取り、全ての `|A| ≤ n` に共通する上界を得た。
有限生成部分構造自身がTのモデルであることは要求しない。
空集合・n=0・不整合理論も含む。これで Fact 2.5 が完成した。

さらに、有限個の型での真理値ベクトルによりQF式を分類し、各QF式がT同値となる
有限代表集合を構成した。各tupleの図式内部にも有限代表集合を取れる。
したがって前回残した Definition 2.2(6) の「finite modulo T」の文字どおりの読みも
完成した。有限連言による図式の表示だけから結論を飛躍させていない。
別担当者も有限被覆・濃度上界・同値類代表・空の場合を独立に照合した。

既存のcanonical semantic universe規約の下でDefinition 2.2の全6項目を完成と登録する。
companion・e.c.・局所有限性でのモデル量化は `Type (max u v)` を用いる。
これらを任意の外部universeへ移すbridgeは独立の残件として保持する。
Fact 2.3の逆方向と一般bounded-amalgamation criterionも未完成である。

## 検証と次の境界

`python3 scripts/check.py` の全6 gateが終了値0・警告0で成功した。
41数学モジュール・1,472宣言を公理監査し、private名の宣言288件を含む。
公開名の1,184宣言について公開性を確認した。依存公理は
`propext`、`Classical.choice`、`Quot.sound` のみ。
検査前後と保存時の入力ハッシュは一致する。
全gateログ・宣言一覧・入力ハッシュは
[固定検証記録](audit-artifacts/2026-09-10/presentation-roots-uniformity/README.md) に保存した。
pin済みcacheによるローカル検証であり、CI実行やmathlib全体のclean rebuildではない。
数学ソースのrevisionは `88d4fa414ea6f4325b55f71fe25d94cac332589e26d49974b601fcc0132b06ee`。
対応表は50項目中31件が `proved`、3件が `partial`、16件が `planned`。
項目数は全体の作業量や完成率を表さない。

次の主な課題は Proposition 4.3 の混合blockをtensorとして同定し、自由表示の
関係部分空間を各blockで計算して、canonicalなη₁–η₃と自然性に接続することである。
外積の左index数による射影だけでは、この同型が完成したとはしない。
旧 `ExteriorSupport.lean` の再利用範囲は今回の射影までであり、その先のcanonicalな
tensor同型は別途構成する必要がある。

次回の具体的な接続順序は以下とする。

1. `Finset.toLeft`、`toRight`、`disjSum` と `card_toLeft_add_card_toRight` を使い、
   外冪基底のindexを左右の部分集合の対で表す。mathlib `Basis.tensorProduct` と
   `exteriorPower.map` がtensor基底と左右の埋め込みの再利用入口となる。
2. `ExteriorSum.block b n k` と `ΛᵏV₀ ⊗ Λⁿ⁻ᵏV₁` の実際の同型を作り、
   原稿の次数2・3で必要な成分に特殊化する。現在のindex順はk=0からnなので、
   原稿の左成分から始まる表示には順序の入れ替えが必要である。
3. 自由表示のkernelからcoproductの商表示を作り、Lemma 4.2とblock quotientを適用する。
   紙面のη₃における `V₀ ⊗ gr₂(G₁)` の写像はLie bracket `[u,q]` であり、
   通常の外積表示のその成分には負符号を合成する。基底選択後の同型だけでなく、
   canonical factor mapsとbracketからの写像との一致・自然性を証明する。

F₂による中心列一致、同時commutator roots、基底に基づく次元評価、`15n²`、
生成元ベースのsupport、一般criterion、主定理と系は引き続き未完成。
数値関数を別のBoundsモジュールへ移さず、原稿の対応箇所で実装する方針を維持する。
