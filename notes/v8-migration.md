# v8 への出典移行

> 履歴資料（v8 原稿）。TeX/PDF は archives に保存。現行版は [v9 移行記録](v9-migration.md) を参照。

2026-09-23。利用者から受領した `main_v8.tex` を内容を変更せず
[T3_modelcompanion_v8.tex](../archives/T3_modelcompanion_v8.tex) として配置した。
SHA256 は `9546045ccd5cb0170ac54fe1485d356765400ed938c57442da558c41c51fa38c`。
旧版は [archives/T3_modelcompanion_v7.tex](../archives/T3_modelcompanion_v7.tex) と
[PDF](../archives/T3_modelcompanion_v7.pdf) を移動し、TeX の SHA256
`fb32d367e325f081eaeaf77b0c680662c9f58d1e8bc2a45adb0436cbe17c3ad6` を保持する。
両ファイルは移動前の Git HEAD と byte 単位で一致する。

## 確認した差分

v7 と v8 の §2–5 は、Fact 2.27 の見出しを
`Levi and van der Waerden's theorem` から
`Levi and van der Waerden \cite{LeviVanDerWaerden1933}` に変更した箇所を除き、
末尾の空白を取り除いたテキストが完全一致する。主張、仮定、定数、主要構成に
変更はなく、これらの項目と部分項目の出典行は一律に 5 行後へ移る。
既存の Lean の数学的宣言はこの移行で変更していない。

序論・参考文献は改訂された。Takeuchi 予想は序論の Conjecture 1.1
（175–177 行、`conj:burnside-model-companion`）として番号と label を得た。
安定 ID `questions.takeuchi_conjecture` は保持し、`open` / `statement_checked`
として登録する。179 行の説明と非表示の旧 §6 により、局所有限性・全有限生成群の
有限性・全有限 rank Burnside 群の有限性という従来の定式化との対応を保つ。
182–184 行の大素数についての別論文予告は、本ライブラリで証明した結果ではない。

旧 §6「Further questions」は v8 の 1464–1547 行の `\if0 ... \fi` 内にあり、
PDF 本文には表示されない。この節の本文は、末尾の空白を取り除くと v7 と完全一致する。
Questions 6.1–6.2 と Burnside 群による局所有限性への還元は、対応表に
`source_status = "inactive"` として残した。旧 §6 の番号は非表示の本文に対する
履歴用の表示であり、v8 PDF の項目番号ではない。旧 §6 の Takeuchi 予想は
Conjecture 1.1 の追加出典として保持する。

## 対応表の範囲と検証境界

v8 の有効な本文は、番号付き 54 項目、Proposition A、§2 の無番号定義 2 項目の
計 57 項目である。既存の証明に対応する 56 項目と未解決の Conjecture 1.1 を区別する。
さらに非表示の 3 項目（証明済みの還元 1 項目、未解決の質問 2 項目）を保持するため、
対応表全体は従来と同じ 60 項目・80 部分項目である。

`scripts/paper_map.py` は `conjecture` 環境と原稿の literal conditional を扱い、
有効な本文だけで theorem counter と項目数を確認する。非表示の項目についても
出典行、状態、既存宣言への対応を別途検査する。

既存の `verification` の record と code revision はそのまま保持する。
`proof_checked` の出典は [v7 形式化記録](v7-formalization.md) と各既存監査記録であり、
今回のテキスト差分確認を、v8 全文の新しい数学的 fidelity review として扱わない。
序論の新しい文献紹介や別論文の予告まで Lean が検証したという意味でもない。
PDF 生成、対応表の整合性、Lean の全体 gate、Palomar の別検査、公開・提出・登録は
それぞれ別の作業である。

## PDF と今回の検証

ルートの [T3_modelcompanion_v8.pdf](../archives/T3_modelcompanion_v8.pdf) は21ページ。
原稿本文を変更せず、次のコマンドで生成してルートへコピーした。

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error \
  -outdir=.audit/v8-pdf T3_modelcompanion_v8.tex
```

最終 LaTeX log に警告・未解決の参照や引用・overfull/underfull box はない。
全21ページを画像化して確認し、序論1–3ページと参考文献20–21ページは詳細表示でも確認した。
Conjecture 1.1 が表示され、旧 Further questions と謝辞の placeholder は出力されない。

Lean の変更117ファイルはコメントのみであり、コメントを除いたコードは移行前と一致する。
原稿 parser の条件分岐処理は、入れ子・else・行位置の保持・不正な条件分岐の拒否を確認した。

`python3 scripts/check.py` は全7段階が終了コード0・警告0で通過し、
検査前後で入力hashが不変だった。`PATH=/home/ywr/.local/go/bin:$PATH
scripts/verify-comparator.sh` も通過し、選択した2定理の比較、NanoDa と Lean
標準カーネルによる Solution の検証に成功した。別検査での Challenge の2つの
意図的な証明穴の警告は、数学ライブラリの警告・未証明箇所とは区別する。
今回は Verso の rendering 検査を再実行していない。

入力hash、各検査log、PDFとアーカイブのhashは
[検証記録](audit-artifacts/2026-09-23/v8-migration/README.md) に保存した。
