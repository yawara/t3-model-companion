# t3-model-companion

*Existence of a Model Companion for Groups of Exponent 3* の Lean 形式化。
対象原稿は [T3_modelcompanion_v4.tex](T3_modelcompanion_v4.tex) です。

現在の実装と最終検証の記録は [論文全体の形式化](notes/paper-faithful-completion.md) を参照。
主定理・model companion の存在に加え、例・remark・記法と一般モデル宇宙への接続を含め、
原稿との対応を [50項目・75部分項目](docs/paper-map.md) で管理しています。

- [Lean で論文を読む入口](T3/Paper.lean)
- [論文項目と実装状況](docs/paper-map.md)
- [モジュール・namespace の方針](notes/lean-architecture.md)
- [実装順序と暫定見積もり](notes/implementation-plan.md)
- [既存実装との初期 fidelity 監査](notes/paper-faithfulness-audit.md)
- [論文の初期数学的検証](notes/paper-mathematical-audit.md)
- [無限正規形・中心列・次数商の検証境界](notes/infinite-normal-form-and-graded-checkpoint.md)
- [graded Lie 構造とモデル完全性の検証境界](notes/graded-lie-checkpoint.md)
- [自由群の外積同型・quotient・有限図式の検証境界](notes/exterior-quotient-diagram-checkpoint.md)
- [自由表示・同時根・一様局所有限性の検証境界](notes/presentation-roots-and-uniformity-checkpoint.md)
- [Coproduct の tensor 分解と model companion 判定の検証境界](notes/coproduct-tensor-and-companion-checkpoint.md)
- [一般 bounded-amalgamation criterion の実装境界](notes/bounded-amalgamation-implementation-frontier.md)
- [Graded coproduct と一般 amalgamation 判定の検証境界](notes/graded-coproduct-and-amalgamation-checkpoint.md)
- [同時交換子 roots・e.c. 群・support の検証境界](notes/commutator-roots-and-support-checkpoint.md)
- [基底による二段階 strictification の検証境界](notes/strictification-checkpoint.md)
- [Strict envelope と amalgam の商表示の検証境界](notes/strict-envelope-and-pushout-checkpoint.md)
- [主定理と model companion の存在の検証境界](notes/main-theorem-checkpoint.md)
- [正次数 graded Lie の定義と生成条件の検証境界](notes/positive-grading-checkpoint.md)
- [Associated graded の例とモデル埋込みの検証境界](notes/examples-and-model-embeddings-checkpoint.md)
- [任意宇宙の意味論と群の記法の検証境界](notes/semantic-universes-and-notation-checkpoint.md)
- [論文全体の最終検証](notes/paper-faithful-completion.md)

過去の監査・検証境界は当時の状態を固定した記録です。現在の証明状況は最終検証と対応表を
参照してください。

Lean/mathlib は v4.32.2、mathlib の commit は
`905b95818eb32af7874a58b427f50c1711a5e96c` に固定しています。
必要なのは [elan](https://github.com/leanprover/elan) と Python 3.11 以上です。

```sh
lake exe cache get
python3 scripts/check.py
```

`scripts/check.py` は build、全数学モジュールの import 登録、mathlib 標準 lint、
全 project 数学宣言の公理依存、論文対応表を検査します。警告も失敗として扱います。
実行ログと入力ファイルのハッシュは `.audit/` に保存します。

新しい数学ファイルを追加した場合は集約を更新します。

```sh
lake exe mk_all --lib T3 --module
```

`mk_all` はファイルを更新した場合にも非零で終了します。
通常の検査では `--check` を使い、更新が不要であることを確認します。

論文の対応情報は `docs/paper-map.toml` を編集してから生成します。

```sh
python3 scripts/paper_map.py --write
```

`planned` の項目には未証明の Lean 宣言を置きません。
Lean の証明状況と原稿との照合状況は別々に表示します。
数値関数は、正規形・strict envelope・主定理それぞれのモジュールで定義します。

文献は `references` サブモジュールにあります。Lean の build と CI に文献の取得は不要です。
文献も読む場合は、アクセス権のある環境で次を実行します。

```sh
git submodule update --init references
```

GitHub Actions も同じ検査コマンドを実行します。
環境の準備と mathlib cache の取得には
[lean-action](https://github.com/leanprover/lean-action) を使用します。
