# v8 paper review evidence (2026-09-24, second pass)

The authored review is [`notes/v8-paper-review-2026-09-24.md`](../../../v8-paper-review-2026-09-24.md).
It covers `T3_modelcompanion_v8.tex`, SHA-256
`9546045ccd5cb0170ac54fe1485d356765400ed938c57442da558c41c51fa38c`.
The manuscript, its PDF, and the Lean sources were not changed.

## Storage

External source material is kept in a separate literature archive under
`references/`. The T3 repository
ignores `/references/` and tracks only this README and the source inventory. Section 27 of
`references/MANIFEST.md` records provenance and SHA-256 for every file added for this review:

- `audit-artifacts/t3-model-companion/2026-09-24/v8-paper-review/sources/arxiv/`:
  arXiv:2609.05789v1 (PDF and text extract) and the raw arXiv API response of 2026-09-24;
- `audit-artifacts/t3-model-companion/2026-09-24/v8-paper-review/sources/crossref/`:
  raw Crossref work records for fifteen DOIs;
- `audit-artifacts/t3-model-companion/2026-09-24/v8-paper-review/sources/msc2020.pdf` and
  `msc2020-excerpt.txt`;
- `rendered-pages/burris-1984/p0068-*.png`, `p0069-*.png` and `p0074-*.png` (180 DPI).

Publication PDFs and page renders registered earlier (MANIFEST sections 21-26) were consulted
in place. [`source-inventory.json`](source-inventory.json) lists, for each cited and each
proposed reference, the manuscript lines, the locator checked, the evidence paths with
SHA-256, the verdict, and the recommended action.

## Build check

A temporary copy of the manuscript was compiled twice with `pdflatex -interaction=nonstopmode`
(pdfTeX 3.141592653-2.6-1.40.25, TeX Live 2023). The second run reported no LaTeX warnings and
no overfull or underfull boxes, and produced 21 pages. The build products were not retained.

## Boundaries

- The review checks the hypotheses, conclusions, language, quantifier ranges and locators of
  the claims the manuscript attributes to its sources. It does not re-verify the cited proofs.
- The derivation of the line-133 statement from Eklof (1972), Theorems 4 and 7, is recorded in
  the review note. It is a corollary obtained in this review, not a statement printed in that
  paper.
- Not verified: the journal numbering of Corollary 4.42 in d'Elbée-Müller-Ramsey-Siniora
  (2025), since the publisher and the AUC repository returned HTTP 403; and possible overlap with
  F. Leinen's work on existentially closed groups in locally finite classes, whose texts could
  not be obtained. The novelty search was not exhaustive.

> Historical redaction: private source locations and internal revision identifiers have been omitted. Mathematical claims and recorded historical check results are unchanged; this does not report a new verification run.
