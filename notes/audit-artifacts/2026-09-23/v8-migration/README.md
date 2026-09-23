# v8 migration verification

Date: 2026-09-23. Source: `T3_modelcompanion_v8.tex`, SHA256
`9546045ccd5cb0170ac54fe1485d356765400ed938c57442da558c41c51fa38c`.

`checks.json` records the exact inputs to `python3 scripts/check.py`:
all seven stages passed with zero warnings and unchanged inputs.
The corresponding stage logs are preserved alongside it.
`comparator.log` records successful statement comparison, NanoDa replay,
and acceptance by Lean's default kernel. Its two Challenge proof-hole warnings
are the intentional specification holes outside the mathematical library.
`migration-checks.json` records source/PDF hashes, archive preservation,
PDF review scope, and the unchanged mathematical Lean code.

The checks verify this local snapshot, not publication, submission, registration,
a new review of every manuscript claim, or a new Verso rendering check.
