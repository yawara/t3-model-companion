# v7 formalization verification snapshot

Date: 2026-09-22. Source: `T3_modelcompanion_v7.tex`, SHA256
`fb32d367e325f081eaeaf77b0c680662c9f58d1e8bc2a45adb0436cbe17c3ad6`.
The detailed scope and source review are in [the verification record](../../../v7-formalization.md).

- `checks.json`: all seven `scripts/check.py` stages passed with zero warnings;
  source hashes were unchanged across the run. The copied command argument for
  `--declarations-json` is normalized to a repository-relative path. No outcomes,
  timings, or source hashes were changed.
- `declarations.json`: the kernel-derived inventory of all 3111 project declarations,
  including private declarations, in 117 source modules; allowed dependencies are
  only `propext`, `Classical.choice`, and `Quot.sound`.
- The seven corresponding logs preserve the individual gate results. Text lint covers
  118 sources, including the independent Challenge specification.
- `v7-comparator.log`: successful comparison of the two selected principal theorems,
  with both NanoDa and the Lean default kernel accepting Solution. The two deliberate
  Challenge holes are outside the mathematical library and are its only expected warnings.
- `new-modules.json`: exact hashes and aggregate digest for the seven new modules.
- `v7-existing-code-comparison.json`: comparison of comment/string-stripped lexical
  code against the pre-migration HEAD for 109 existing modified Lean files. The two
  aggregators are excluded because they gained imports. Source fidelity was also
  reviewed directly; this lexical check is not a natural-language proof audit.

This is a local uncommitted source snapshot, not a submission or publication record.
The paper map records 57 proved items, all 80 parts proved, and three open problems.
