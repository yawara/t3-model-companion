# Palomar submission preparation and Lean v4.34.0

> Historical T3 revision identifiers have been omitted for publication. Recorded commands, outcomes, and source hashes describe the original checks; this edited record does not certify the rewritten historical snapshots.

> 履歴資料（v7 原稿）。原稿と PDF は [archives](../archives/README.md) に保存。現行版への移行は [v8 移行記録](v8-migration.md) を参照。

2026-09-22. This checkpoint reviews local submission preparation against current
Palomar requirements. It does not record a submission, editorial review, or
registration. The repository was confirmed private through GitHub's API.

## Scope and source

The starting historical revision is omitted from this publication record. The source is `T3_modelcompanion_v7.tex`, SHA256
`fb32d367e325f081eaeaf77b0c680662c9f58d1e8bc2a45adb0436cbe17c3ad6`.
The manuscript and the selected Challenge statements are unchanged.
The paper map retains 57 proved items, 80 proved parts, and three open items.
The additional Section 6 research notes remain outside the Lean proof scope.

The formalization author and responsible maintainer is Yawara Ishida.
The manuscript authors are Yawara Ishida, Ryosuke Mizuno, and Kota Takeuchi.
The metadata accurately distinguishes agent review from human peer review.

## Current upstream requirements and pins

The audit uses PalomarPolicy
[`792c7c0b9e798bd02719e795ef11fa2b5929e067`](https://github.com/PalomarRegistry/PalomarPolicy/blob/792c7c0b9e798bd02719e795ef11fa2b5929e067/CONTRIBUTING.md)
and PalomarSubmission
[`a09f5c38ee58bf92c459b974b174ff4063ebea5f`](https://github.com/PalomarRegistry/PalomarSubmission/tree/a09f5c38ee58bf92c459b974b174ff4063ebea5f).
The recorded minimum remains Lean v4.28.0. The latest stable Lean and mathlib
release is v4.34.0, and exact matching exporter and Verso tags exist.

| Component | Selected version or revision |
| --- | --- |
| Lean | `leanprover/lean4:v4.34.0` |
| mathlib | `5ed2965256430c3649e86755f9576b54eca72435` |
| lean4export | `076e8e57707e813375e8f9da8bf989799ace9680` |
| Verso (isolated rendering check) | `cad4b633e75ea769b851f12f9ca3b4f0dfcc625f` |
| Comparator | `575674928e239f5bc452aab72d1dd7b0f1326494` |
| NanoDa | `68d5ca9db226849b41a6fff59d796ff19d0a8840` |
| Landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` |

The project, authenticated mathlib revision, exporter source, and Verso source
all declare exactly Lean v4.34.0. Comparator, NanoDa, and Landrun match the
current Palomar workflow pins. The regenerated project manifest matches
mathlib's exact transitive dependency revisions and public HTTPS GitHub URLs.
The existing formalization.yaml v0.4 schema and taxonomy snapshots still match
upstream, so no schema migration is required.

## Migration and independent statement review

The update replaces deprecated conditional lemmas, a finite-Sigma import, and
the surjective commutativity alias with their current names. Tensor-product
induction uses the new eliminator, whose pure-tensor case already supplies the
zero case. Equal-subset equivalences use `Set.equivOfEq`. The generalized
graded-bracket API receives the same grading for both arguments, with its
index action explicitly reduced to addition. One graded equivalence proof
applies its existing representative lemma directly. A v7 source-line typo in
the witness-bound docstring is corrected from 812 to 810. Lean declaration
locators in the paper map are regenerated where lines moved.

These are API and proof-elaboration changes. Mathematical hypotheses, bounds,
and principal constructions are preserved; no linter is suppressed and no
project axiom or proof hole is introduced. Independent review also checked
the Challenge/Solution boundary, the equivalence of finiteness and finite
generation in this setting, the total generator bound, and the established
bridges from canonical to arbitrary model universes.

The mathematical source snapshot is
`sha256:502a2cd6da001c744181daf367c8307039f028cf968f93b370020a59acc776dd`,
computed from the sorted JSON path-to-SHA256 dictionary for `T3.lean` and
`T3/**/*.lean`. It identifies local source contents, not a submission commit.

## Verification

All local verification gates passed on v4.34.0. The
[saved evidence](audit-artifacts/2026-09-22/palomar-readiness/README.md)
records the exact inputs and results.

- `python3 scripts/check.py` passed all seven stages with zero warnings and
  unchanged inputs: metadata, build, imports, environment lint, text lint,
  axiom audit, and paper-map validation.
- Text lint covers 118 source modules without exceptions. The axiom audit
  covers 3,120 declarations in 117 source modules, including private
  declarations. Only `propext`, `Classical.choice`, and `Quot.sound` occur.
  This checks all declarations irrespective of use; it is not an unused-code
  analysis or a claim that private declarations are unused.
- Comparator accepted both selected statements and their definition closures.
  NanoDa and Lean's default kernel both accepted the Solution. The separate
  Challenge build emitted exactly the two expected deliberate-hole warnings.
- The paper-map check matched the kernel declaration inventory and the v7
  source. The three open items remain open.

Compared with the previous toolchain, the declaration inventory changes from
3,111 to 3,120 entries. Additions and removals are compiler-generated proof,
auxiliary, and constructor-index declarations. No handwritten declaration was
added or removed. The inventory comparison is not a type-equivalence proof;
the independent source review and Comparator checks provide separate evidence.

Verso successfully elaborates, extracts, and renders the actual unchanged
Challenge, using the pinned mathlib cache without importing the proof library.
Both selected theorem anchors are recognized by the current upstream static
HTML parser. Extraction and HTML rendering emit no warnings; Challenge
elaboration emits only the two deliberate theorem-hole warnings. This checks
the actual statement rendering, not the complete Palomar sandbox, asset
sanitization, or editorial review.

The build uses mathlib's pinned cache; a clean source rebuild of all
dependencies is not claimed. The cache update lacked two upstream artifacts,
which Lake handled during the successful build. Isolated Verso setup also
reports the upstream SubVerso missing-manifest warning; this is separate from
the zero-warning project mathematical gate and the clean rendering commands.

## Submission boundary

The prepared repository has no tracked compiled Lean/native artifacts, Git
LFS pointers, symlinks, or submodules. Its tracked contents were approximately
12.1 MB before adding this checkpoint, below Palomar's 500 MiB limit. The
Challenge is below the policy's line and byte warning thresholds. The root
license, source attribution, author/maintainer fields, source-based result
origin, and two selected declarations satisfy the current local metadata audit.

Actual submission still requires a public GitHub snapshot and its full
40-character commit SHA. Publishing, submission, and final registration were
not requested or performed. Remote CI and Palomar's own mechanical/editorial
workflow are distinct from these local checks. Manuscript editorial
placeholders are disclosed and remain outside the formalized claims.

The local technical preparation is complete. The source changes and this
verification evidence remain available for review before choosing a submission
commit and making it publicly accessible.
