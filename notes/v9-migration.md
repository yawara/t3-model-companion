# v9 への移行とリポジトリ全体のレビュー

> Historical T3 revision identifiers have been omitted for publication. Recorded commands, outcomes, and source hashes describe the original checks; this edited record does not certify the rewritten historical snapshots.

2026-09-25。v8 の TeX/PDF を変更せずアーカイブし、受領した `main_v9.tex` を
[T3_modelcompanion_v9.tex](../T3_modelcompanion_v9.tex) として現行原稿にした。
**利用者の指示に従い、v9 の TeX 本体は受領ファイルとバイト単位で同一である。**
原稿への指摘は別ノートに記録し、適用していない。
この方針は `AGENTS.md` にも記録した。

- 受領・現行 v9 SHA256: `d48f10716bcc7963b654c6fe27013ac75eaa9cbdf6593683a0efc513dd062952`。
- [アーカイブ v8 TeX](../archives/T3_modelcompanion_v8.tex):
  `9546045ccd5cb0170ac54fe1485d356765400ed938c57442da558c41c51fa38c`。
- [アーカイブ v8 PDF](../archives/T3_modelcompanion_v8.pdf):
  `f50936d88ae7184d32eecda64ca2142ca9cc9ff13d4f5a5dad0cb49a9760e4a6`。

v8 の二ファイルは移行前 HEAD `[historical revision omitted]` と
バイト同一である。[保存・比較記録](audit-artifacts/2026-09-25/v9-review/migration-checks.json)
に記録した。作業中に一度適用した原稿変更は利用者の指示によりすべて取り消した。
[未適用の修正案](audit-artifacts/2026-09-25/v9-review/unapplied-manuscript-suggestions.patch)
は検討用の差分であり、現行原稿・配布 PDF には反映しない。

## 数学のレビュー

受領 v9 の §2–5 は v8 と完全一致する（末尾の空白行を除く）。
主張の位置は一律に 10 行後へ移り、Conjecture 1.1 は 5 行後へ移る。
それを確認した上で、原稿の全項目と主要な Lean 宣言・証明経路を再読した。

- [§2–3 の照合](v9-prelim-main-review.md): 一般モデル理論の量化順序、有限部分構造、
  任意宇宙への bridge、正規形・graded の公開境界、両因子の非 amalgamation 証人、
  `f(m) = 15 * ((3*m+4) * (m + choose(m,2) + choose(m,3)) + 1)^2`。
- [§4–5 の照合](v9-constructions-review.md): 自由表示と tensor 商、strict coproduct、
  `F₂` による中心列一致、同時 root 構成、e.c. 移送、`15n²` の上界、共有 roots、
  反例の cardinal rank と有限生成の場合への bridge。
- [序論・参考文献・公開情報の照合](v9-reference-publication-review.md): 改訂された
  Eklof、Maier、Novikov–Adian／Adian の帰属と所在、形式化の著者・対象範囲。

仮定の追加、上界の緩和、有限 rank への制限を必要とする数学的な不一致は見つからなかった。
数学的 Lean コードの変更はない。117 Lean ファイルの変更は出典・行・説明のコメントのみであり、
入れ子コメントと行コメントを除き、文字列を含む残りのバイトが移行前 HEAD と一致する。
低層の全補助証明を一行ずつ再監査したという主張ではない。

## 原稿への指摘（未適用）

詳細は上記のレビュー記録に残す。主な指摘は次のとおり。

1. Eklof の JEP 版は Theorems 4・7 からの帰結として帰属を明確にできる。
   Eklof–Sabbagh と Maier の定理番号も付記できる。
2. 可解長の「高々 n」、先行研究についての断定の射程、coproduct の商における
   非 amalgamation 証人の説明を明確にできる。
3. 原稿の形式化記述は、第一著者 Yawara Ishida と §2–5 の証明対象を明記する余地がある。
   一般予想・別稿の大素数結果は形式化に含まれない。リポジトリのメタデータでは区別する。
4. 理論変数、Pi₂、有限図式、無限 rank の有限支持、生成元数の「高々」、
   Corollary 3.4 の適用条件、§4 の G、Example 5.1 の H、自由生成元名に明確化の余地がある。
5. Theorem 3.3 と序論の Main Theorem の表題、著者名の後の空白、長い DOI の組版は
   別途検討事項として残す。Novikov–Adian Part II の 241–479 頁は正しく、そのまま保持する。

これらは原稿本体への変更ではない。本文、著者情報、所属・研究助成、AI 開示、
label、仮定・定数・証明の記述はすべて受領時のまま保存した。

## 現行原稿とアーカイブの対応

v9 は旧 §6 を削除しており、v8 のような `if0` 内の保持ではない。
対応表は有効 57 項目（56 証明済み、Conjecture 1.1 は open）と、アーカイブ v8 の
3 項目（既知の還元 1 件、open の質問 2 件）を区別する。合計 60 項目・80 部分項目。
既存の Burnside 群と局所有限性の同値は維持し、一般予想の証明へ読み替えない。
一部 Lean docstring の詳細出典は、同じ本文を持つアーカイブ v7 §6 のまま保持する。

`docs/paper-map.toml` にアーカイブのパスと hash、および項目ごとの `source_path` を追加した。
`paper_map.py` は両版の hash、元の行・label、active/inactive、未解決状態を検査する。
`check.py` の入力記録も対応表から現行原稿とアーカイブを取得する。
旧検証記録・既存の `verification` は当時の検証対象のまま残し、今回の記録を別に保存した。
README、AGENTS、構成方針、fidelity 案内、Palomar メタデータ、Challenge/Solution の
出典、履歴ノートの現行版への案内を v9 に合わせた。
Palomar の外部ポリシー・schema についての記述は、既存の 2026-09-22 時点の確認として
過去形にし、今回の remote 再確認を示す現在形の記述を改めた。

## PDF と機械検証

受領原稿をそのまま `latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error`
でコンパイルし、[v9 PDF](../T3_modelcompanion_v9.pdf) を生成した（21ページ）。
最終 PDF の全21ページを新たに画像で確認した。作業途中の修正案を反映した22ページ版は
配布対象ではなく、その目視確認を最終版の確認へ転用していない。

受領原稿に由来する組版所見として、1ページの著者名の後の空白が詰まり、21ページの
Novikov–Adian の DOI 最終行は本文の右端を約19.07pt超える。後者の字間が広い3行も含め、
文字はすべて用紙内に収まり、欠落・重なりはない。TeX変更禁止の指示に従い原稿を維持した。
未解決の参照・引用と LaTeX Warning は0件、overfull hbox は1件、underfull hbox は3件。
[PDF確認記録](audit-artifacts/2026-09-25/v9-review/pdf-review.json) に記録した。

`PATH=/home/ywr/.local/go/bin:$PATH scripts/verify-comparator.sh` は通過し、
選択した二定理を Comparator で比較した。NanoDa と Lean の標準 kernel が Solution を受理した。
この検査だけに現れる Challenge の意図的な二つの `sorry` 警告は、数学ライブラリとは別である。

最終スナップショットの `python3 scripts/check.py` は全8段階が終了コード0・警告0で通過し、
検査前後の入力 hash は不変だった。metadata、12件の対応表 regression tests、build、
import 集約、mathlib environment/text lint、公理監査、kernel inventory に基づく対応表を検査した。
公理監査は 117 モジュールの 3,120 宣言を対象とし、
許可された `propext`、`Classical.choice`、`Quot.sound` 以外を使用していない。
依存パッケージは固定版と既存キャッシュを使用し、全依存のクリーン rebuild とは称しない。

今回の [検証記録](audit-artifacts/2026-09-25/v9-review/README.md) に入力 hash、
各段階の log、Comparator/NanoDa、PDF の log と目視確認範囲を保存した。
途中の入力変更や中断のある検査を最終状態の成功記録として扱っていない。
最後に追跡済み差分の `git diff --check`、現行文書のローカルリンク、原稿とアーカイブのバイト一致も確認した。
コミット前に新規ファイルも含めて検査すると、受領 TeX、生の LaTeX log、未適用 patch の
文脈行に末尾空白等がある。元のバイトを保持し、その他の staged 差分は空白検査を通過した。
詳細は検証記録の `precommit-whitespace.json` に保存した。

## 検証の境界

自然言語と Lean の対応は agent による読解であり、自然言語の意味の機械的認証でも
独立した人間の査読でもない。原典の全証明と新規性の網羅的な文献調査は対象外。
d’Elbée ほかの Corollary 4.42 は出版社配布著者原稿で確認した番号であり、
最終組版版の番号の再照合は未実施である。

Conjecture 1.1 と旧 §6 の一般的質問は open のまま。十分大きい素数についての
別稿の証明はこのリポジトリには含めない。Palomar の公開・提出・登録、remote CI は
今回実行していない。Challenge の二つの意図的な証明穴は数学ライブラリから独立した仕様に限る。
