# arXiv publication and Palomar preparation evidence

This directory records the local checks described in the
[2026-09-25 checkpoint](../../../arxiv-publication-2026-09-25.md).

- `source-comparison.json`: the public arXiv v1 source and the pinned local v9
  manuscript match byte-for-byte, without normalization.
- `metadata-source-checks.json`: the public source metadata is accepted, while
  a local-only identifier, missing local path, and missing hash are rejected.
- `checks.json` and the eight gate logs: all project checks passed with zero
  warnings and unchanged inputs on Lean/mathlib v4.35.0-rc2. Repository-root
  prefixes in command arguments and logs are made relative for publication.
- `axiom-summary.json`: 3,120 declarations in 117 source modules use only the
  three permitted axioms; text lint covers 118 modules without exceptions.
- `publication-inputs.json`: hashes of the publication files and the complete
  local declaration manifest at this checkpoint, with confirmation that all
  gate inputs matched then. Later README and AI-disclosure edits are not inputs
  to this historical snapshot.
- `comparator-checks.json`: the current sandboxed comparison is blocked at
  the host preflight; the separate legacy comparison accepted both statements
  and replayed the Solution with NanoDa and Lean. It does not certify con-ron.
- `verso-checks.json`: actual Challenge extraction, HTML rendering, and both
  theorem anchors passed on the matching Verso release. Upstream tool-build
  warnings are recorded separately from the project's zero-warning gate.

Downloaded paper archives, PDFs, binaries, dependency caches, and compiled
proof artifacts are excluded. Local checks do not constitute repository
publication, Palomar submission, editorial review, or registration.
