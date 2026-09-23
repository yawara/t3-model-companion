# 2026-09-24 pre-commit verification

The user requested committing and pushing all pending work, including the
v8 source migration and reference review. `python3 scripts/check.py` passed
all seven stages with zero warnings and unchanged input hashes. Exact inputs
and timings are in `checks.json`; each stage's output is retained alongside it.

The v8 TeX/PDF and archived v7 TeX/PDF retain the hashes recorded in the
2026-09-23 migration report. No manuscript citation correction was applied
as part of the reference review; its proposed changes remain in the notes.

External publication material is stored in a separate literature archive. The parent
`.gitignore` still excludes `/references/`, and the parent index contains
no files or gitlink under that path. The raw review evidence was moved
without changing bytes; its relocation/hash inventory is retained in the
adjacent `v8-reference-review/evidence-storage.json`.

The checked input hashes exactly match the previously recorded v8 migration
check. Comparator/NanoDa/Lean-kernel results for that unchanged snapshot
remain in the 2026-09-23 migration record; they were not rerun here.

> Historical redaction: private source locations and internal revision identifiers have been omitted. Mathematical claims and recorded historical check results are unchanged; this does not report a new verification run.
