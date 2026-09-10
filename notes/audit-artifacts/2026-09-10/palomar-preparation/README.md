# Palomar preparation verification

2026-09-10. Local verification of the substantive proof development and its two
selected statement declarations. No remote CI execution, publication, submission,
registration, or human peer review is asserted.

## Statement and kernel comparison

`comparator.log` records a successful run of the pinned Comparator with NanoDa
enabled. Its last lines report acceptance by NanoDa, acceptance by Lean's default
kernel, and `Your solution is okay!`. The process exited 0.
`comparator-verification.json` records the exact command, tool environment,
revisions, and input hashes. All recorded input hashes were checked against the
live files when preserved.

- Comparator: `575674928e239f5bc452aab72d1dd7b0f1326494`.
- lean4export: `86e4a339507466921dc8c5417c8cb1de1ce7df60` (Lean v4.32.2).
- NanoDa: `68d5ca9db226849b41a6fff59d796ff19d0a8840`.
- Landrun: `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`.

The selected declarations are `T3.exists_bounded_nonamalgamation_witness` and
`T3.has_model_companion`; there are no definition holes, and the only permitted
axioms are `propext`, `Classical.choice`, and `Quot.sound`.
Challenge's two deliberate theorem-hole warnings are expected in this separate
specification check. The proof-library gate requires zero warnings.

`exponent-sentence-defeq.lean.txt` preserves a separate Lean probe, which exited 0
with no warnings. Its `rfl` proof confirms that the explicit bound-variable index
in `exponentSentence` gives exactly the previous definition. It is an audit
artifact outside the mathematical import graph.
`source-comparison.json` records a comparison against the preceding mathematical
snapshot: documentation changed in 33 T3 files, and the explicit finite index is
the only change to mathematical code. Copyright headers were preserved.

## Full project gate

`checks.json` records all seven stages passing with exit 0 and zero warnings,
and verifies unchanged inputs during the run. All 134 input hashes also
matched the live files when the artifacts were saved. The corresponding
seven logs and `declarations.json` preserve the actual outputs and inventory.

- Axiom audit: 2,972 declarations in 110 source modules, including Solution.
- Text lint: 111 source modules, including Challenge; no exceptions.
- Public names: 2,393. The only removed name is the generated auxiliary proof
  `FirstOrder.Group.exponentSentence._proof_1`; all retained declarations have
  unchanged modules, export flags, and axiom dependencies.
- Actual and permitted axioms: `propext`, `Classical.choice`, `Quot.sound`.
- Paper map: all 50 items and 75 parts are proved and proof_checked.
- Mathematical revision:
  `305b6338d4129eb20885ccb54e9b994451a2eba3b479aaf41c3508f55135fccc`.

`public-api-comparison.json` records the inventory comparison. This local run
used the pinned Lean/mathlib cache; it is not a clean rebuild of mathlib.

See the [preparation checkpoint](../../../palomar-preparation.md) for scope and
[Palomar documentation](../../../../docs/palomar.md) for the selected statements.
