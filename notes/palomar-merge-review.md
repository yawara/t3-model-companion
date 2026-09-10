# Palomar preparation integration review

> Historical T3 revision identifiers have been omitted for publication. Recorded commands, outcomes, and source hashes describe the original checks; this edited record does not certify the rewritten historical snapshots.

2026-09-10. Reviewed the preparation commit
`[historical revision omitted]` against main at
`[historical revision omitted]` before integration.
The review covered the entire preparation diff, with separate agent reviews
of the statement boundary, verification and CI, and public metadata.

## Findings and resolution

Two source locators in `Challenge.lean` were off by two lines:
`freeOrderExponent` referred to line 732 instead of line 730, and
`witnessBound` referred to line 734 instead of line 732. The two numbers were
corrected against the source manuscript. Removing comments from the old and
new Challenge files yields identical Lean code.

No additional actionable findings were found in the selected theorem
statements, hypotheses, explicit bounds, universe bridges, permitted holes
and axioms, verification scope, CI configuration, author roles, current
publication tree, mathematical citations, or copyright headers.

The manuscript has three authors; Yawara Ishida is the sole formalization
author and responsible maintainer. The mathematical library and the source
manuscript are unchanged by this review fix. The mathematical source revision
remains `305b6338d4129eb20885ccb54e9b994451a2eba3b479aaf41c3508f55135fccc`.
The preceding [preparation record](palomar-preparation.md) and its frozen
artifacts retain their original inputs.

## Verification and integration

On the corrected inputs, `python3 scripts/check.py` passed all seven stages
with exit 0 and zero warnings. It audited 2,972 declarations in 110 source
modules and text-linted 111 modules with no exceptions. The complete declaration
inventory is byte-identical to the preparation inventory. The paper map still
contains 50 proved / proof_checked items and 75 parts.

`scripts/verify-comparator.sh` was then run end to end and exited 0.
Comparator accepted the selected statements and definitions; NanoDa and Lean's
default kernel both accepted the solution. The two intentional Challenge-hole
warnings remain confined to this separate specification check. All 134 project
input hashes matched after both checks.

[Verification artifacts](audit-artifacts/2026-09-10/palomar-merge-review/README.md)
preserve the actual logs, input hashes, fixed tool revisions, and inventory
comparison. These corrected, verified inputs are ready for fast-forward
integration into main.

The independent reviews inspect the current change and its evidence; they do
not constitute a new line-by-line review of all prior proof bodies or human
peer review. Remote CI, publication, and submission were not performed.
