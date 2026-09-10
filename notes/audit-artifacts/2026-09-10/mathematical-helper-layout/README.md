# Mathematical helper layout verification

2026-09-10. All six stages of `python3 scripts/check.py` passed with exit 0 and zero warnings.
Input hashes remained unchanged during the gate and matched the live files when saved.
This is local verification using the pinned Lean/mathlib cache.

- Source modules: 109, down from 110 after merging the exterior-index preparation.
- Audited declarations: 2,973. Public names: 2,394, all exported.
- Public-name sets, export flags and axiom sets match the preceding paper-completion snapshot.
- Actual and permitted axioms: `propext`, `Classical.choice`, `Quot.sound`.
- Paper map: all 50 items and 75 parts remain proved and proof_checked.
- Mathematical revision: `92a68de03c4ad4fe992d652a08f33cb9a8d9c3027ce5650dd7ea40d7dbbfbd2e`.

`checks.json` records all inputs and stage results. `declarations.json` records every audited
declaration. The six logs and `public-api-comparison.json` preserve the verification evidence.
The public API comparison concerns declaration names, exports, modules and axiom sets;
independent source review checked preservation of statements, variable scopes and proof text.

See [the layout record](../../../mathematical-helper-layout.md) for the change and review scope.
The preceding paper-fidelity record and its frozen artifacts remain unchanged.
