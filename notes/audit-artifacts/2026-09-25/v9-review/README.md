# v9 migration and final verification, 2026-09-25

The active v9 TeX is byte-identical to the supplied manuscript. The v8 TeX/PDF
are byte-identical to the pre-migration HEAD. `migration-checks.json` records
the received and archived hashes, the unchanged non-comment Lean code, and
the final PDF hash. The manuscript suggestions are **unapplied** and are
retained only in `unapplied-manuscript-suggestions.patch` and the review notes.

`checks.json` records the final stable snapshot: all eight stages passed with
zero warnings and unchanged input hashes. The added source-map fixture suite
has 12 tests; the remaining stages cover metadata, build, import aggregation,
mathlib environment/text lint, every project declaration's axioms, and the
paper map against the exported kernel inventory. Each stage log is retained.
Earlier in-progress runs are not used as final verification records.

`comparator.log` records successful comparison of the two selected statements
and successful replay by NanoDa and Lean's default kernel. Challenge's two
intentional proof-hole warnings are confined to this separate specification
check. No mathematical-library proof holes or extra axioms are permitted.

`latex.log` and `latexmk.log` belong to the unchanged received TeX, producing
the delivered 21-page PDF. All 21 pages were visually inspected afresh.
`pdf-review.json` records the page hashes and the two source-origin typography
findings: tight author spacing and the final bibliography's long DOI line.
The latter extends 19.07228pt beyond the text margin but stays inside the page;
no text is clipped or overlapped. TeX was preserved as instructed.

Natural-language fidelity, kernel proofs, exact source preservation, PDF
inspection, and local Palomar preparation are separate claims. External
publication, registration, submission, remote CI, and independent human peer
review were not performed. The source conjecture and archived questions
remain open. Details are in `notes/v9-migration.md` and its three review notes.

The precommit index check also covers newly added files. It reports existing
trailing whitespace in the verbatim supplied TeX, raw LaTeX logs, and context
lines of the unapplied patch. Those bytes are intentionally preserved; no
mathematical linter was disabled. `precommit-whitespace.json` records these
findings. The remaining staged files pass `git diff --cached --check`.
