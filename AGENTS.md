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
- Place shared generic helpers in modules for their mathematical subject, and construction-specific
  helpers alongside the construction. Do not introduce a separate `ForMathlib` layer. Preserve native
  namespaces and `Paper-ID` correspondence when moving declarations.
- Credit Yawara Ishida as the sole formalization author and responsible maintainer. The manuscript
  authors are Yawara Ishida, Ryosuke Mizuno, and Kota Takeuchi. Keep these authorship roles distinct.
- Keep publication material self-contained and preserve mathematical source citations and copyright
  headers. Do not include confidential locations or internal working notes.
- Prepare Palomar files locally. Publishing the repository, submitting, and registering a result
  are separate actions requiring the user's instruction.
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
- `Challenge.lean` is an independent Mathlib-only specification outside the mathematical graph;
  only its two selected theorem proofs may contain deliberate holes. `Solution.lean` imports the
  complete proofs. Keep both outside `T3` aggregation and run the separate Palomar checks.
