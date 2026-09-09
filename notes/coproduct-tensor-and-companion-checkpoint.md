# Coproduct の tensor 分解と model companion 判定の検証境界

2026-09-10。対象は `T3_modelcompanion_v4.tex`、SHA256
`79745dfa1660a827c51ec3c6b2006ee9d6243cb4702f97a75e5b55357b89f50b`。
これは論文全体の完成ではない。全体 goal は有効なまま維持する。

今回の全ライブラリ検査は6段階すべて警告0で成功した。入力ハッシュを再照合し、
[検査成果物](audit-artifacts/2026-09-10/coproduct-tensor-companion/README.md) を保存した。

## Fact 2.3 の両方向

`ModelTheory/ModelCompanionCriterion.lean` の
`isModelCompanionOf_iff_models_iff_isExistentiallyClosed` は、一般の Π₂ 理論について
model companion と e.c. class の公理化の同値を証明する。
旧リポジトリの e.c. 拡大・elementary chain・Robinson test を再利用した。

一段拡大では、元のモデル上で同時に実現可能な存在条件の集合を compactness と
Zorn の補題で極大にする。これを ω 回反復する。旧コードの普遍理論の仮定が使われていた
直極限のモデル性は、今回 `PiTwoDirectLimit.models_of_isPiTwo` で一般 Π₂ に拡張した。
有限 tuple を共通段階へ持ち上げて存在量化を処理し、同値な ∀∃ 公理化を通じて元の理論へ戻す。
有限言語・局所有限性・amalgamation の仮定は加えていない。

逆向きの model completeness は、存在式を反映する埋め込みから交互拡大列を作る
Robinson test を使う。二段合成の初等性と elementary chain theorem から埋め込みの
初等性を得て、既存 `AllEmbeddingsElementary.isModelComplete` により、各式と
T 同値な存在式を実際に生成する。意味論的条件で止めていない。

モデル量化は既存の `Type (max u v)` 規約である。この規約の下で Fact 2.3 全体が完成した。
任意の上位宇宙での companion/e.c. 定義との移行補題は別の残件として保持する。
主担当と独立担当が全5モジュールの数学・仮定・宇宙境界を照合した。

## 原稿の coproduct 表示と関係部分群

`Coproduct/Presentation.lean` は、指定された全射 `Free I → G₀`、`Free J → G₁` に対し、
`Free (I ⊕ J)` を左右の kernel の像の join の normal closure で割る原稿の商を構成する。
`quotientEquiv` は、その商と通常の自由積の cube quotient である `Coproduct G₀ G₁` の
canonical な群同型である。生成元・因子・逆写像の公式を持ち、合成 presentation の
全射性と kernel が指定 normal closure に等しいことを証明する。
この部分の仮定は左右の全射性のみである。

左右の関係部分群が derived subgroup に入る場合、join はその積になる。
retraction を用い、任意次数でその積と lower central term との交差が成分ごとに分かれる
ことを証明した。関係部分群そのものを homogeneous と仮定していない。
`AssociatedGraded/Subgroup.lean` は、retraction を持つ写像に沿って ambient graded image
を輸送する一般補題を与える。`Coproduct/Relations.lean` がこれを接続し、normal closure の
次数1・2・3の関係部分空間を、各自由因子内で計算した像により記述する。

正規部分群の ambient graded image は全 ambient layer との bracket に閉じる。
これにより、原稿の `Rᵢ ∧ Vᵢ ⊆ Sᵢ` が正規性から従うことを明示した。
正規性は元の因子内でのみ要求し、輸送後の部分群が全 coproduct 内で正規とは仮定しない。
さらに次数1の左右因子像が全体を生成することから bracket の4項を展開し、
`subgroupImage_relationKernel_three_eq_four_blocks` で原稿の
`S = S₀ + [R₀,V₁] + [V₀,R₁] + S₁` まで証明した。
ここで右の混合項の符号を消せるのは部分空間の等式だからであり、写像の等式ではない。

## 外積と tensor の canonical な同型

`ForMathlib/PowersetCardSum.lean` は、左右の添字型に有限性を仮定せず、固定された大きさの
部分集合を左右の部分集合の対へ分ける。
`ExteriorTensor.tensorEquiv` は、これと mathlib の exterior basis・tensor basis を組み合わせ、
任意の可換環上の基底付き加群に対して

`Λⁿ(V₀ × V₁) ≃ₗ ⨁ k : Fin (n+1), ΛᵏV₀ ⊗ Λⁿ⁻ᵏV₁`

を構成する。左右の基底は任意 rank を許す。次数0も含む。
左添字が右添字に先行する lex 順序を用い、union の基底が符号 +1 の順序付き外積に
なることを証明した。

`wedgeMap` は基底を使わず、実際の `exteriorPower.map` による左右の包含と乗法から定義する。
`tensorEquiv_symm_comp_lof` は各成分上で逆同型と `wedgeMap` が一致することを証明し、
`tensorEquiv_symm_toLinearMap` は逆同型全体がこれらの和であることを証明する。
したがって座標だけの同型ではない。
`blockTensorEquiv` は前回の `ExteriorSum.block` を実際の tensor 積と同定し、
その underlying map が `wedgeMap` であることも保持する。

`Free/ExteriorNaturality.lean` は、自由群準同型と指定線形写像の次数1での一致から、
次数2・3での σ と exterior-power map の一致を証明する。
特に左右の `Free.map (Sum.inl/inr)` が実際の exterior inclusion に移る。
有限 rank・準同型の単射性・Sum 上の包含の単調性は不要である。
末尾の3つの混合 bracket の式は `(1,1)`、`(2,1)`、`(1,2)` についてそれぞれ
符号 `+,+,−` を持つ。最後の負符号も Lean で明示して証明した。
外積・関係像・σ の追加は実装担当とは別の担当も読解し、原稿と照合した。

## Canonical な η と残っている接続

`Coproduct/Graded.lean` には η₁ の実際の線形同型、η₂・η₃の線形写像、
tensor の定義式と全体の自然性を実装した。写像は基底を選ばない。
η₁ の両側逆写像は因子への retraction から証明した。この次数だけは紙面の
presentation・外積経由を短縮して coproduct の普遍性を直接用いるが、写像は同じである。
η₂・η₃の全単射性と block 間 bracket 包含は未証明なので、Proposition 4.3 は `partial`。

η₃ の `(1,2)` 成分は原稿どおり `[inl x, inr q]` で定義する。
この成分を通常の順序付き外積の tensor block と結ぶときには負符号を合成する必要がある。
次数の並びは外積分解では k=0,…,n、論文の表示では左因子から始まるため、並べ替えも必要。

次の接続は、関係部分空間を外積の各 block に輸送して quotient を取り、これらの
canonical η₂・η₃と合成写像が一致することを証明することである。
block quotient は既存 `BlockDecomposition.quotientEquiv`、tensor quotient は mathlib の
`TensorProduct.quotientTensorEquiv`、`tensorQuotientEquiv` と代表元公式を利用できる。
後者は `Mathlib/LinearAlgebra/TensorProduct/Quotient.lean` の105–147行にある。
混合関係空間の kernel 計算には同 `RightExactness.lean` の303・405・427行の補題も使える。

その後も strict coproduct、非自明 G と F₂、同時 commutator roots、基底に基づく次元評価、
`15n²` envelope、生成元数に基づく support、一般 bounded-amalgamation criterion、
主定理・系・残る例と記法が未完成である。

モデル理論側の次の接続は [一般 bounded-amalgamation criterion の実装境界](bounded-amalgamation-implementation-frontier.md)
に整理した。有限構造 A・B・C 自体に T-model 条件を加えず、共通の上界を選ぶ量化順と
総生成元数を保つ。まず model companion から bounded obstruction を得る必要方向を扱う。
これは実装計画であり、Fact 2.6 の証明済み部分としては数えない。

## 全ライブラリ検証

`python3 scripts/check.py` が build、import 登録、environment lint、text lint、
公理監査、論文対応表の6段階すべて exit code 0・警告0で成功した。
固定済み Lean/mathlib のローカル cache を用いた検証であり、mathlib の clean build や CI 実行ではない。

- 数学モジュールは集約を含めて53。
- 公理監査は private を含む1,789宣言。private 名309、public 名1,480で、public 名はすべて export 済み。
- export 済み監査対象は1,484名。private 定義から生成された equation lemma 4件も含むため、
  private と exported のフラグは排他的ではない。
- 実際の公理依存は `propext`、`Classical.choice`、`Quot.sound` のみ。`sorryAx`・独自公理はない。
- 論文対応表は全50項目中 `proved` 32、`partial` 3、`planned` 15。
  数学的難度に重みを付けた完成率ではなく、Fact 2.6・主定理等は未完成である。
- 数学ソース revision は
  `ab88bd971dc348f35c07e9402f1ee244391eaad8fd3709962be1a7c7a111b7d8`。
  `T3.lean` と `T3/**/*.lean` の path-to-SHA256 辞書を `json.dumps(..., sort_keys=True)` した SHA256 である。
- 全検査入力のハッシュは `checks.json`、宣言ごとの可視性・公理依存は `declarations.json` に保存した。

前回の固定記録は [自由表示・同時根・一様局所有限性](presentation-roots-and-uniformity-checkpoint.md)
とその成果物ディレクトリに保持する。
