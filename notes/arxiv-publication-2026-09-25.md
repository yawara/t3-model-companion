# arXiv 公開と Palomar 準備の更新

確認日: 2026-09-25。

## 公開論文とローカル原稿

*Existence of a Model Companion for Groups of Exponent 3* は
[arXiv:2609.30061](https://arxiv.org/abs/2609.30061) として公開されている。
著者は Yawara Ishida、Ryosuke Mizuno、Kota Takeuchi。
[v1](https://arxiv.org/abs/2609.30061v1) の投稿日時は
2026-09-24 16:20:58 UTC である。

[v1 のソース](https://arxiv.org/src/2609.30061v1) に含まれる `main_v9.tex` と
リポジトリの `T3_modelcompanion_v9.tex` は、改行等の正規化なしでバイト単位で一致した。
いずれも 73,483 bytes、SHA256 は
`d48f10716bcc7963b654c6fe27013ac75eaa9cbdf6593683a0efc513dd062952`。
原稿 TeX と既存 PDF は変更していない。

README を外部の読者向けに整理して公開論文へのリンクを掲載し、
`formalization.yaml` の出典 ID を公開 URL に更新した。
Palomar 用の説明、Challenge と Solution の文書コメントにも出典を記載した。
公開論文の ID と、対応表の行番号を固定するローカル原稿パス・ハッシュの両方を
メタデータ検査で確認する。

README の AI 利用表記は簡潔な “AI agents” とし、詳細メタデータには
OpenAI Codex と Claude の利用方法を記載した。正確なモデル版は特定しない。

形式化の著者・責任保守者は Yawara Ishida 一人であり、論文の三著者とは区別する。
Conjecture 1.1、アーカイブ由来の質問、別稿予告は従来どおり証明済み範囲に含めない。

## Palomar の現行要件

確認した PalomarSubmission の版は
[`a59f25bd8a66bf6faf3a4f4260d412989c0185ea`](https://github.com/PalomarRegistry/PalomarSubmission/tree/a59f25bd8a66bf6faf3a4f4260d412989c0185ea)。
[最低 Lean 版](https://github.com/PalomarRegistry/PalomarSubmission/blob/a59f25bd8a66bf6faf3a4f4260d412989c0185ea/toolchains.json)
は `v4.35.0-rc2` に更新されている。従来の `v4.34.0` はこの最低版を満たさないため、
Lean と mathlib を `v4.35.0-rc2` に揃えた。
これは release candidate への移行である。

mathlib は `065356127b1dc0016f66b7283ce0ce2c4055aa55` に固定し、
推移的依存関係も `lake-manifest.json` に記録する。
数学ライブラリの互換性修正は11ファイルで、`ZMod 3` の標準環から得られる
加法群構造の明示、既存の消去等式の型指定、部分群の包含・有限生成性 API の更新である。
定理文・仮定・定数・主要構成は保持し、新規の公理・証明穴・linter 抑制は加えていない。
宣言の位置が動いた12箇所を対応表へ反映して Markdown を再生成した。
別担当の差分レビューでも、対応表の変更が行番号だけであることを確認した。

依存キャッシュは 8,869 / 8,915 件の取得後に進行が止まったため、取得を中断し、
必要な残りを固定ソースから構築した。全依存関係をクリーンビルドしたという記録ではない。
従来の [2026-09-22 検証](palomar-readiness-2026-09-22.md) と
[v9 移行検証](v9-migration.md) は、それぞれの入力・ツールチェーンについての履歴として保持する。

現行 Palomar の比較は Lean 配布物に含まれる `lake comparator`、`leanexport`、
`leanchecker` と、独立カーネル NanoDa・con-ron を使う。
`scripts/verify-comparator.sh` をこの構成へ更新した。
公開用の `comparator.json` は保持し、実行時だけ独立カーネルの絶対パスを
一時的な設定ファイルへ記録する。

CI には固定した upstream installer による bubblewrap 0.12.0 の準備を追加した。
installer の SHA256 は
`c290df6cebdf1cb26edb69ed4164d9551062bfeb65243b93d1d1d3b77eac0a35`。
実行手順とホスト要件は [Palomar 用文書](../docs/palomar.md) に記録した。

## 検証

`python3 scripts/check.py` は全8ゲートを警告0・入力ハッシュ不変で通過した。
メタデータ、対応表の回帰検査、全体ビルド、imports、環境 lint、テキスト lint、
公理監査、Lean 宣言一覧と対応表の照合を含む。
テキスト lint は118モジュールを例外なしで検査し、公理監査は117ソースモジュールの
3,120宣言を検査した。依存公理は `propext`、`Classical.choice`、`Quot.sound` のみである。

補助検証として、従来の Comparator・NanoDa・Landrun の固定版を保持し、exporter を
`v4.35.0-rc2` の `6cea97789dc088ea47fcea15692db85685aedac5` に揃えた比較を実行した。
両選択宣言の比較が通り、NanoDa と Lean の既定カーネルが Solution を受理した。
警告は Challenge の意図された二つの証明穴だけである。
これは旧ツール構成による補助検証で、以下の現行 Palomar ゲートの成功とは区別する。

Verso `v4.35.0-rc2`（`9f8096e40b31715b1d8d5997f15a0bd832f7e37d`）で
実際の `Challenge.lean` を分離環境から処理し、文書抽出・HTML 出力と、
二つの選択定理のアンカーを現行 upstream parser で確認した。
Challenge の elaboration は意図された二つの証明穴の警告のみ、抽出・HTML 出力は
警告・エラーとも0だった。表示ツール自体のセットアップには SubVerso の警告1件、
Verso のビルドには upstream の警告6件があり、T3 の警告ゼロ検査とは区別する。
これは表示互換性の確認であり、Palomar の完全な隔離・sanitization 処理の再現ではない。

現行比較スクリプトは実際に起動し、このホストの bubblewrap 0.9.0 が要件を
満たさないため事前検査で停止した。別のプローブでもユーザー名前空間の作成が
ホストに拒否されることを確認した。**現行の sandboxed Comparator と con-ron の
検証成功は主張しない。** ホスト設定の変更やサンドボックスの無効化は行っていない。
CI のセットアップは静的に確認したが、リモートの CI 実行は今回行っていない。

[保存済み証拠](audit-artifacts/2026-09-25/arxiv-publication/README.md) には、
取得ソースの一致判定、メタデータの整合性検査、および各検証の範囲を記録する。
これは初回の公開対応時点の入力を記録したもので、後続の README 整理と
AI 利用表記の変更後のファイルハッシュへ置き換えない。

## 公開・登録との区別

論文の arXiv 公開と形式化リポジトリの公開は別の状態である。
今回の作業はローカルの公開情報・依存関係・検証手順の更新であり、
リポジトリ公開、Palomar 投稿、編集審査、結果登録は行っていない。
