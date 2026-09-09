# 最初の Lean 実装

2026-09-09。Lean/mathlib v4.32.2、mathlib commit
`905b95818eb32af7874a58b427f50c1711a5e96c`。
対象は v4 TeX、SHA256
`79745dfa1660a827c51ec3c6b2006ee9d6243cb4702f97a75e5b55357b89f50b`。

## 数学的な実装範囲

- `T3/GroupTheory/Basic.lean`：自明群を含む `HasExponentThree`、
  `Monoid.exponent G ∣ 3` との同値、TeX 324–325 の集合の交換子部分群。
- `T3/GroupTheory/Identities.lean`：Fact 2.15 の項目 1、2、4–11。
  項目 3 は derived subgroup の可換性まで。Z₂ が非可換になり得る具体例は未実装。

公開宣言の所在は [対応表](../docs/paper-map.md) に登録する。
Fact 2.15 全体の状態は `partial` とする。Notation 2.1 全体や後続の自由群・正規形・
associated graded・model companion の主張を完了したとは扱わない。

## 原稿との対応の確認

交換子は mathlib の `a*b*a⁻¹*b⁻¹` を使う。原稿の共役 `g⁻¹*a*g` は
`commutator_conjugates` の型に明示している。
逆元・積の恒等式は項目 5、8、9 の引数順と符号で公開した。
項目 10、11 は任意の `Set G` を受け、原稿どおり交換子を生成する部分群を作り、
右辺を部分群の pointwise な集合積として扱う。

中心列は mathlib の既存定義を用いる。`lowerCentralSeries 2` が原稿の γ₃、
`lowerCentralSeries 3 = ⊥` が γ₄=1 に対応する。
`commutator_triple_cyclic` を繰り返し適用して原稿の三つの巡回表示を得られ、
`commutator_self_right` が 2-Engel 性を与える。

主要な計算は Yawara Ishida による以前の指数 3 群の基本恒等式と冪零性の
形式化から、必要な依存だけ移した。元の著作者・著作権表示を保持している。
Levi–van der Waerden の原典と基本恒等式の数学的確認は
[数学的監査](paper-mathematical-audit.md) を引き継ぐ。
新たな集合の包含式は、原稿の積の恒等式を部分群の生成元に適用して証明した。
原稿の仮定・定数を変更していない。

## 検査とソースの同定

数学ソース4ファイルの SHA256 を、相対パスをキーとする辞書にして
`json.dumps(inputs, sort_keys=True)` で直列化し、さらに SHA256 を取った識別子は
`546edf575b27afe80eea1fd59089c5566fd4cf9297af6b51f06688b9fe1d51db`。
対応表の `code_revision = "sha256:..."` はこのソース状態を指す。Git commit と混同しない。

`python3 scripts/check.py` は公開対応表に実在する宣言を登録した状態で、
全6検査を警告0で通過した。公理検査は4数学モジュール・130宣言を対象とし、
private 名の宣言78件を含む。52宣言が `T3` から公開されていることも確認した。
最終の入力ハッシュ・検査結果・宣言一覧・ログは
[検査記録](audit-artifacts/2026-09-09/lean-initialization/README.md) に保存した。

公理検査は source module によって全 project 数学宣言を選ぶ。
private データを明示的に読み込み、標準 namespace や未使用の private 宣言も確認する。
別の公開環境で、対応表の宣言が `T3` から利用できることも確認する。
許容公理は `propext`、`Classical.choice`、`Quot.sound` のみ。
負例では、未使用 private axiom と標準 namespace 内の axiom の両方を検出して失敗した。
検査用の反例は独立した一時ディレクトリに作り、数学ソースへ追加していない。

初期依存キャッシュは、同じ pin の既存 `.lake/packages` を独立コピーして利用した。
`lakefile.toml` と manifest は Git の依存を宣言し、隣接 repo への path dependency はない。
今回のローカル検証はキャッシュを使う通常の build であり、mathlib 全体の clean rebuild
および GitHub Actions 上での実行を報告するものではない。

## 次の境界

自由指数 3 群と正規形を独立に移植し、有限性と `t(n)` を
`T3/GroupTheory/Free/NormalForm.lean` で公開する。
同時に、上記の Z₂ の非可換例を自由群 F₂ から回収する。
続いて標準 Lie API を使う associated graded を構成する。

> 公開履歴の整理に伴い、非公開の作業場所・内部識別子を省略した。数学的記述と当時の検証結果は保持しており、ここに記す検証は当時の対象に限る。
