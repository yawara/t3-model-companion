# Complete v4 paper verification

2026-09-10. All six stages of `python3 scripts/check.py` passed, exit 0 and zero warnings.
Input hashes matched the live files when these artifacts were saved.
This is local verification using the pinned Lean/mathlib cache, not a clean mathlib build or CI.

- Mathematical source modules, including aggregation entrypoints: 110.
- Audited declarations: 2,973; private names: 579; public names: 2,394, all exported.
- Exported names: 2,411, including 17 generated private equations/splitters.
  Private and exported flags are not mutually exclusive.
- Actual and permitted axioms: `propext`, `Classical.choice`, `Quot.sound`.
- Paper map: all 50 items and all 75 parts are proved and proof_checked; no partial/planned items.
- TeX SHA256: `79745dfa1660a827c51ec3c6b2006ee9d6243cb4702f97a75e5b55357b89f50b`.
- Mathematical source revision: `0895205ed3ac7498330f87694e712d6e89edda228a294a628eaa1885557d3de5`.

The mathematical revision hashes the JSON serialization (`sort_keys=True`) of the source
path-to-SHA256 dictionary. All input hashes, kernel declarations and six stage logs are included.
Build, imports, environment lint, text lint, axiom audit and paper-map checks took
2.549, 0.575, 2.343, 6.4, 213.059, 0.271 seconds, respectively.

The library proves the main witness theorem with the paper's explicit bound and unconditional
model-companion existence. Examples, notation, arbitrary ranks and semantic universes are included.
Remark 4.10 uses actual shared-generator F4/F3 quotients and their strictification conclusions.
Fact 2.6 has both directions with ordinary amalgams in arbitrary target universes.

The included shared-root review is a snapshot from before final integration. Its temporary
module names were replaced only in imports on promotion. The final criterion also received
agent source/type/proof review; its canonical restriction preserves generators. The snapshot
does not purport to have certified the subsequent full-library gate.

See [the completion record](../../../paper-faithful-completion.md) for source-fidelity scope,
the exact mathematical statements and representations, reuse, and validation limits.
Machine-generated input manifests and gate logs are preserved as records of this revision.
