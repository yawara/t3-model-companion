# Palomar preparation checkpoint

2026-09-10. This repository is the substantive formalization of
*Existence of a Model Companion for Groups of Exponent 3*.
Yawara Ishida is the formalization author and responsible maintainer.
The manuscript authors are Yawara Ishida, Ryosuke Mizuno, and Kota Takeuchi.
The repository remains private; this checkpoint does not publish or submit it.

## Statement and proof boundary

`Challenge.lean` states Theorem 3.3 and Corollary 3.4 with concrete mathematical
definitions and exactly two deliberate theorem proof holes. It imports only
Mathlib. `Solution.lean` imports their completed proofs from the mathematical
library. Challenge is excluded from default builds, the mathematical import
graph, and the proof-library axiom audit; its source is included in text lint.
Solution is included in default builds, text lint, and the axiom audit.

The selected declarations are `T3.exists_bounded_nonamalgamation_witness` and
`T3.has_model_companion`. The bound, hypotheses, and principal constructions
are unchanged. All 50 paper items and 75 parts remain within the paper map's
scope; Comparator checks the two selected results and their dependencies.

`FirstOrder.Group.exponentSentence` spells out its bound variable as
`&⟨0, Nat.zero_lt_one⟩` in place of `&0`. These denote the same element of `Fin 1`
and are definitionally equal by proof irrelevance. The explicit proof avoids
Lean's module-dependent sharing of generated auxiliary proofs, allowing the
independent statement module and proof library to compare identically.
Other mathematical source changes in this checkpoint concern module documentation.
Paper-ID, TeX source labels, and copyright attribution are preserved.

## Reproducibility and verification

The manuscript, Lean v4.32.2, and mathlib
`905b95818eb32af7874a58b427f50c1711a5e96c` are unchanged.
Metadata follows formalization.yaml v0.4; the local validator uses the vendored
schema, classification lists, source hash, and the two-result configuration.
`scripts/verify-comparator.sh` pins Comparator, the matching Lean exporter,
NanoDa, and Landrun. These checks run locally and in separate GitHub Actions
jobs; neither job publishes or submits the project.

The mathematical source revision is
`305b6338d4129eb20885ccb54e9b994451a2eba3b479aaf41c3508f55135fccc`.
It is the SHA256 of the JSON-encoded, sorted path-to-SHA256 dictionary for
`T3.lean` and `T3/**/*.lean`. The paper map points to this revision and record.
`python3 scripts/check.py` passed all seven stages with exit 0 and zero
warnings: metadata, build, import aggregation, environment lint, text lint,
axiom audit, and paper map. The 134 recorded input hashes remained unchanged
throughout the run and matched the live files when the evidence was saved.
The audit covers 2,972 declarations in 110 source modules (the 109 T3 modules
and Solution); text lint covers 111 modules, including Challenge, with no
exceptions. Only `propext`, `Classical.choice`, and `Quot.sound` occur as axioms.
All 50 paper items and 75 parts are `proved` / `proof_checked`.

The pinned Comparator passed with exit 0; both NanoDa and Lean's default
kernel accepted the selected solution. Its two Challenge theorem-hole
warnings belong to the independent specification, outside the proof-library
gate. There are no definition holes. The matching exporter uses Lean v4.32.2.
Exact tool revisions and commands are recorded in the
[verification artifacts](audit-artifacts/2026-09-10/palomar-preparation/README.md).

The declaration inventory differs from the preceding checkpoint only by the
removal of `FirstOrder.Group.exponentSentence._proof_1`, a generated auxiliary
proof made unnecessary by the explicit index. All handwritten declarations
retain their names, modules, export status, and axiom dependencies. The current
inventory has 2,393 public names. This is local verification using the pinned
Lean/mathlib cache; it does not assert a clean rebuild of mathlib or a remote
CI run.

The preceding [mathematical helper layout checkpoint](mathematical-helper-layout.md)
and its frozen machine verification artifacts describe the earlier snapshot.
Paper fidelity remains the recorded agent review of source statements,
hypotheses, constants, and principal constructions. Neither the local gate nor
the independent kernel replay constitutes human peer review or Palomar approval.
