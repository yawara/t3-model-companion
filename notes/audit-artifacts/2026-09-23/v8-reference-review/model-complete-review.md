# v8 reference review: abelian and model-complete pure groups

Audit date: 2026-09-23. Manuscript was not changed. This is a reference-fidelity review, not a review or formal verification of every proof in the cited papers.

## Scope and verdict

| v8 source line | Reference | Status |
| --- | --- | --- |
| 133 | Eklof--Fischer 1972 | Bibliography checked; precise original theorem and its inductive + JEP hypotheses remain unverified because original full text was not obtained. Do not mark as a demonstrated error. |
| 147 | Hoffmann--Kowalski--Tran--Ye | Matches latest original preprint, v2, Theorem 3.3, p. 18. |
| 147 | Frącek--Kowalski | Matches latest original preprint, v2, Theorem 3.6, p. 10. |
| 1502 | Eklof--Sabbagh 1971 | This occurrence is inside the disabled `\if0 ... \fi` section and is not active PDF prose. Bibliography checked; original full-text correspondence remains unverified. |

## Hoffmann--Kowalski--Tran--Ye

Original source: https://arxiv.org/html/2312.08988v2#S3.Thmtheorem3 and https://arxiv.org/pdf/2312.08988v2 . Theorem 3.3 is on printed/PDF p. 18 (rendered and inspected). Its assumptions are a model-complete field K and a split semisimple algebraic group G over K; both G(K) and its commutator group are model complete. The pure group language is explicit in the preceding Theorem 3.1 and throughout the interpretation/embedding argument. In the paper, saying a structure is model complete means that its complete first-order theory is model complete.

Thus v8's existential wording “some semisimple algebraic groups” is true and does not overstate the theorem. A more informative citation would say “groups of rational points of split semisimple algebraic groups over model-complete fields” and cite Theorem 3.3. This is a precision improvement, not a mathematical correction. The following distinction in v8 between complete theories of particular groups and model companions of group varieties is also appropriate.

Bibliography: the author names, title, and arXiv identifier match. Initial submission was 2023-12-14; current v2 is dated 2025-03-02. Describing it as a 2023 preprint is valid but adding the version/date would remove ambiguity because the theorem changed between versions. The unversioned arXiv page currently points to v2.

## Frącek--Kowalski

Original source: https://arxiv.org/html/2512.09414v2#S3.Thmtheorem6 and https://arxiv.org/pdf/2512.09414v2 . Theorem 3.6 is on printed/PDF p. 10 (rendered and inspected). For any field K, it asserts the equivalence between model completeness of K in the ring language and of H(K) in the group language; H(K) is the upper unitriangular 3 by 3 matrix group. No characteristic restriction is imposed. The intermediate proof of a field interpretation uses two named group elements, but the final model-completeness conclusion is for the pure group and does not retain them.

Hence v8:147 states the forward implication correctly. The post-citation sentence that these are complete theories of particular groups is supported by the source's Definition 3.3, not a confusion with a theory of all nilpotent groups.

Bibliography: names (including Frącek), title, and arXiv identifier agree. Initial submission was 2025-12-10; current v2 is dated 2026-02-08. “preprint (2025)” correctly records initial release, but a version/date locator would improve reproducibility.

## Eklof--Fischer

v8:133 attributes to this source existence of a model companion for every inductive theory of abelian groups with JEP. This needs a precise original theorem locator before it can receive the same verified status as the two arXiv citations.

DOI metadata from the publisher and Crossref confirms: Paul C. Eklof and Edward R. Fischer; *The elementary theory of abelian groups*; Annals of Mathematical Logic 4 (1972), no. 2, 115--171; DOI https://doi.org/10.1016/0003-4843(72)90013-7 . The spelling “Fischer” is confirmed by Crossref; some contemporary secondary citations spell “Fisher”, which is not grounds to change v8.

The separately accessible primary abstract for Eklof's *Some model theory of abelian groups*, JSL 37 (1972), 335--342, concerns **complete inductive** theories and identifies those with model-complete theories. That is a different assertion and must not be used as verification of the stronger inductive + JEP sentence: https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/some-model-theory-of-abelian-groups/723738E35EF8C76F5D17F141746CE62B .

Access boundary: Elsevier's article API returned OA metadata without full text; `view=FULL` required an API key; ScienceDirect PDF returned HTTP 403. No primary theorem text or number was inferred from these metadata.

## Eklof--Sabbagh

The source-only sentence at v8:1502 states that the theory of all abelian groups has a model companion, as a counterexample to the converse from companion existence to local finiteness. Its argument using Z to refute local finiteness is mathematically correct. It is disabled in the current manuscript PDF.

DOI metadata confirms: Paul Eklof and Gabriel Sabbagh; *Model-completions and modules*; Annals of Mathematical Logic 2 (1971), no. 3, 251--295; DOI https://doi.org/10.1016/0003-4843(71)90016-7 . The original full text was unavailable under the same boundary as EF. Later literature points to the coherent-ring criterion (Theorems 4.1 and 4.8), which would apply to Z-modules; this is only a search locator and is **not** recorded as direct primary-source verification.

## Evidence files

- `references/audit-artifacts/t3-model-companion/2026-09-23/v8-reference-review/sources/hkty-2312.08988v2.pdf`
- `references/audit-artifacts/t3-model-companion/2026-09-23/v8-reference-review/sources/fk-2512.09414v2.pdf`
- `references/audit-artifacts/t3-model-companion/2026-09-23/v8-reference-review/sources/ef1972-crossref.json`
- `references/audit-artifacts/t3-model-companion/2026-09-23/v8-reference-review/sources/es1971-crossref.json`

Remaining work: obtain EF and ES original full text and record the actual theorem/page; do not silently turn the partial access boundary into a positive fidelity verdict.
