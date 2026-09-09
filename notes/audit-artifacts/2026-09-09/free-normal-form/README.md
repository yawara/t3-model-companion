# 有限正規形の検査記録

2026-09-09。実装と原稿照合の範囲は
[検証境界](../../../free-normal-form-checkpoint.md) を参照。

`python3 scripts/check.py` を全12数学モジュールに対して実行し、全6検査が成功した。
警告0、検査前後の入力ハッシュは一致している。

- `checks.json`：対象ソースのハッシュ、全コマンド、終了値、警告数、実行秒数。
- `declarations.json`：全504数学宣言の由来・private名・公開性・公理依存。
- `build.log`、`imports.log`、`environment-lint.log`、`text-lint.log`、`axioms.log`、
  `paper-map.log`：各コマンドの出力。

private名の宣言113件を含み、391宣言が公開される。許容される依存公理は
`propext`、`Classical.choice`、`Quot.sound` のみで、全宣言がこの条件を満たした。
全数学ソースの辞書ハッシュは
`0987ef1d84e8a33728c7653ca76ef5d030ca4573f86091d87cf271f692712bec`。

これは pin 済み mathlib のキャッシュを使ったローカル検証である。
GitHub Actions の実行や、mathlib 全体の clean rebuild を記録したものではない。
