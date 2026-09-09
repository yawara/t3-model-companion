# 無限正規形・中心列・次数商の検査記録

2026-09-09。数学的範囲と残件は
[検証境界](../../../infinite-normal-form-and-graded-checkpoint.md) を参照。

`python3 scripts/check.py` の全6検査が成功し、終了値0・警告0だった。
検査前後と保存時の入力ハッシュを照合した。

- `checks.json`：入力ファイルのハッシュ、全コマンド、終了値、警告数、実行秒数。
- `declarations.json`：全692数学宣言の由来・private名・公開性・公理依存。
- `build.log`、`imports.log`、`environment-lint.log`、`text-lint.log`、`axioms.log`、
  `paper-map.log`：各検査の出力。

全18数学モジュールを監査し、private名135宣言を含み、557宣言が公開される。
依存公理は `propext`、`Classical.choice`、`Quot.sound` のみ。
全数学ソースの辞書ハッシュは
`e2760b67d2a0dfc9fb89001661f5eab529216bf08b2da05919b9aa9bc180bad0`。

これは pin 済み mathlib のキャッシュを使ったローカル検証である。
Lie bracket、一般criterion、最終model companionの形式化完成を示す記録ではない。
