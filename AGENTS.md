# Working on this formalization

- The source is `T3_modelcompanion_v4.tex`. Follow its statements, hypotheses, constants, and
  principal constructions. Read the relevant source passage before implementing a paper result.
- Read `notes/lean-architecture.md` for the module and namespace policy. Track implementation in
  `docs/paper-map.toml` and regenerate `docs/paper-map.md` with `python3 scripts/paper_map.py --write`.
- Every paper-facing declaration has a docstring with its `Paper-ID` and original TeX label when
  one exists. Keep paper numbering out of mathematical declaration names.
- Distinguish Lean proof status from fidelity review status. A partial result does not complete a
  paper item. Do not add hypotheses or weaken bounds to make an implementation fit.
- If the source and a proposed Lean statement disagree, localize the discrepancy and record the
  source, statement, and reasoning before changing the mathematical claim.
- Use mathlib definitions and namespaces where appropriate. Keep the pinned toolchain and manifest
  reproducible. This repository contains the substantive formal proof development.
- Reuse and copy prior exponent-three proofs wherever their statements and constructions fit
  the paper. The user explicitly authorizes code copying. Adapt imports, names, and source locators;
  concentrate new proof work on actual gaps in the paper correspondence.
- Define numerical functions in their corresponding mathematical modules: the normal form,
  strict envelope, and main theorem. Do not introduce a separate `Bounds` module.
- Do not put `sorry`, `admit`, or project axioms into the mathematical library. Pending results
  belong in the paper map. Preserve source attribution and copyright headers when migrating code.
- Run `python3 scripts/check.py` for a completed change. Require zero warnings, all project
  mathematical sources covered by lint, and only `propext`, `Classical.choice`, and `Quot.sound`
  in the axiom audit. Do not suppress linters to accommodate new code.
- After adding modules, regenerate imports with `lake exe mk_all --lib T3 --module`. This command
  can return nonzero because it updated the aggregator; `--check` must pass afterward.
- Keep audit/test programs outside the mathematical import graph. `T3.lean` and `T3/Paper.lean`
  are aggregation entrypoints, not imports for lower-level mathematical modules.

> Historical redaction: private source locations and internal revision identifiers have been omitted. Mathematical claims and recorded historical check results are unchanged; this does not report a new verification run.
