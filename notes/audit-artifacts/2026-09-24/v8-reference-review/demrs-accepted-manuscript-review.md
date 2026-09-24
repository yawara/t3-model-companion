# d’Elbée–Müller–Ramsey–Siniora: accepted-manuscript supplement

Date: 2026-09-24. Independent, bounded source check of the additional PDF against the active v8 introduction. No manuscript or aggregate audit metadata changed by this review.

## Verdict

The supplied publisher manuscript contains **Corollary 4.42 on internal/PDF page 33**, with the proof continuing on page 34. It directly states the existence of a model companion in the **pure group language** for the relevant nilpotent prime-exponent theory. The corollary and its proof agree mathematically with the previously checked arXiv v3 passage. The mathematical verdict on `T3_modelcompanion_v8.tex:144` therefore remains supported.

The new file verifies the numbering in a **publisher-provided accepted manuscript**, in addition to arXiv v3. It does **not** verify the numbering or journal-page location in the final typeset Version of Record.

## Evidence identity and edition boundary

- Supplied attachment: `/home/ywr/.codex/attachments/083c5017-6795-4bd1-bd4e-9f01b666fde3/1-s2.0-S0021869324004757-am.pdf`.
- Preserved PDF: `references/alternatives/delbee-muller-ramsey-siniora-2025-publisher-accepted-manuscript.pdf`.
- PDF SHA-256: `241e5f99376967a32488919b165a47cdb3432089b0c05d2fc652032a21946356`.
- Extracted text: `references/extracted-text/delbee-muller-ramsey-siniora-2025-publisher-accepted-manuscript.txt`.
- Prior arXiv v3 PDF/text: `references/audit-artifacts/t3-model-companion/2026-09-23/v8-reference-review/demrs2025.{pdf,txt}`; PDF SHA-256 `54ff26d744f7314a57268279a85114c9d5777b86e30276e5957470387ed32cdb`.
- v8 source SHA-256: `9546045ccd5cb0170ac54fe1485d356765400ed938c57442da558c41c51fa38c`.

The new PDF has 46 pages and internal pagination 1–46. Page 1 carries the date August 28, 2024, a manuscript identifier, a link headed “Version of Record,” and the Elsevier manuscript user-license notice. Together with the attachment filename ending `-am.pdf`, these identify this evidence as the publisher manuscript, rather than the final journal composition. The first-page link points to the [Version of Record landing page](https://www.sciencedirect.com/science/article/pii/S0021869324004757); it does not make the supplied manuscript itself that version. The cited journal range 640–701 comprises 62 pages and is not the pagination of this file.

## Source locators and mathematical scope

| Locator in supplied manuscript | Verified content | Consequence for v8 |
| --- | --- | --- |
| §2.3, pp. 8–9; Facts 2.13–2.14, p. 9 | Lazard correspondence is stated for an **odd prime** `p` with `c < p`, for groups/Lie algebras of nilpotency class **at most** `c`. It applies to pure languages as well as languages expanded by a Lazard series. | Preserve `c < p`. For the nonabelian range `c ≥ 2`, primality and `p > c` already force `p` odd. |
| §4.1 and Definition 4.1, p. 14 | Section fixes a natural number `c` and prime `p > c`. The finite classes explicitly have nilpotency class `≤ c`; the construction initially names predicates for a Lazard series. | “c-nilpotent” means class at most `c`, not exactly `c`. The construction's expanded language must not be mistaken for the corollary's final language. |
| Corollary 4.39, p. 32 | The relevant Fraïssé-limit theory has quantifier elimination in the expanded language. | This alone would not settle the pure-group assertion. |
| Proposition 4.41, pp. 32–33 | The named series is the lower central series and coincides with the upper central series in the limit. | Provides the definability step needed to remove the extra predicates. |
| Corollary 4.42, p. 33 | The theory of `G_{c,p}` in `{multiplication, inverse, identity}` is the model companion of the theory of c-nilpotent groups of exponent `p`. The analogous pure Lie-ring reduct is also treated. | This is a direct match to the cited model-companion assertion, not merely an amalgamation result or a claim about an expanded language. |
| Proof of Corollary 4.42, pp. 33–34 | The series predicates have both existential and universal definitions in the Lie-ring reduct. Any c-nilpotent Lie algebra can be equipped with its lower central series and embedded into an expanded model; one then forgets predicates and transfers by Lazard correspondence. | No extra named-series hypothesis is imposed on the original groups, and the target models are not restricted to finite groups. |

The v8 sentence covers prime `p` in general. The only positive-class case with `p = 2` and `c < p` is `c = 1`, the abelian case. The displayed Lazard facts in this source explicitly assume odd `p`, so that exceptional case should be credited separately to the elementary abelian case / Maier's already verified Theorem 3.5. It is not a mathematical counterexample to v8 and does not require changing v8's bound.

## Comparison with arXiv v3

The stored [arXiv v3](https://arxiv.org/abs/2310.17595v3) and the supplied manuscript both place Corollary 4.42 on p. 33 with proof ending on p. 34. Direct comparison of the corollary, preceding language-reduct paragraph, definability equivalences, and embedding/Lazard proof finds the same mathematical claims, hypotheses, and proof route. Differences in the extracted text at this passage are layout/line-order artifacts, including positioning of the superscript `grp`; no substantive change was found in this bounded comparison. This is not a claim that the two entire papers are identical.

Visual verification used the new manuscript's rendered pages 1, 33, and 34; the surrounding definitions and assumptions were also checked in extracted text. The original v8 source was inspected at line 144. No broader proof audit or final journal-page verification was performed.

## Recommended reporting language

“Corollary 4.42, pp. 33–34, verified in both arXiv v3 and the publisher-provided accepted manuscript dated August 28, 2024; the pure-group model-companion assertion and class bound agree with v8. Correspondence of the corollary number with the final typeset journal edition remains unverified.”

No mathematical amendment to v8 is indicated by this additional source. Do not upgrade the remaining edition-specific uncertainty to ‘final published numbering verified’ on the strength of this PDF alone.
