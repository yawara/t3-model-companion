# v8 reference review: solvable and nilpotent group results

Audit date: 2026-09-23. Read-only review of the manuscript. No TeX or Lean edits.

Manuscript: `T3_modelcompanion_v8.tex`, SHA-256 `9546045ccd5cb0170ac54fe1485d356765400ed938c57442da558c41c51fa38c`.

## Verdict and coverage

No mathematical mismatch was identified in the assigned claims. This is **not** a claim that every cited original full text was inspected. The pure-group-language issue is resolved positively by the actual text of d'Elbee et al. Corollary 4.42. Saracino 1976 is directly verified from the original publisher abstract, including the torsion-free case. Saracino 1974, Saracino-Wood 1979 and Maier 1989 have the direct-source limitations recorded below.

| v8 location | Claim | Verdict and evidence boundary |
|---|---|---|
| line 138 | No model companions for fixed solvable derived-length bounds at least 2 | Consistent with the author's own AMS 1974 announcement. The cited Trans. AMS article full text was not obtained. Clarify that the bound is “at most n, for each n >= 2.” |
| line 139 | For each c >= 2, neither class <= c nilpotent groups nor the torsion-free subclass has a model companion | Directly matches Saracino 1976 publisher abstract. Full-text theorem number and proof not inspected. |
| lines 102-104, 143 | Fixed arbitrary finite exponent, nilpotency class <= 2: model companion exists | d'Elbee et al. Remark 4.43 explicitly attributes this result for m in N to Saracino-Wood 1979. Direct original 1979 theorem statement remains uninspected. No evidence of an omitted “odd prime” restriction. |
| lines 103-104, 144 | Prime p, c < p: model companion exists, obtained from Maier's amalgamation | Direct mathematical statement verified in d'Elbee et al. Corollary 4.42, with c < p inherited from the group construction in Corollary 4.39 and the Lazard correspondence. Maier original full text uninspected; the attribution is corroborated by d'Elbee et al. pp. 2-3. |
| lines 104-105, 169 | The above class-2 and c < p results do not cover all exponent-3 groups | Correct scope comparison: the class-2 result excludes class 3, and c = p = 3 is outside c < p. This does not claim that no other literature covers T3. |
| lines 1473-1483 | Repeats positive results; these varieties are locally finite; unbounded-exponent class <= c varieties are not locally finite | These lines are **inactive TeX**, inside `\\if0` at line 1464 through `\\fi` at 1547; they are not present in the current PDF. Repeated reference claims have the same evidence status as above. The local-finiteness statements are mathematically correct: finitely generated nilpotent torsion groups are finite, whereas the unrestricted nilpotent varieties contain Z. |

## Original sources and exact locators

### d'Elbee, Mueller, Ramsey, Siniora

- Verified author manuscript: [arXiv:2310.17595v3](https://arxiv.org/abs/2310.17595v3), posted 21 June 2024, 45 PDF pages. The PDF date printed on p. 1 is 24 June 2024.
- [PDF](https://arxiv.org/pdf/2310.17595v3), downloaded locally as `references/audit-artifacts/t3-model-companion/2026-09-23/v8-reference-review/demrs2025.pdf`; SHA-256 `54ff26d744f7314a57268279a85114c9d5777b86e30276e5957470387ed32cdb`.
- Corollary 4.39, p. 32: the expanded class of finite c-nilpotent exponent-p groups is a Fraisse class when c < p. Quantifier elimination here is in the expanded language with a Lazard series.
- Proposition 4.41, pp. 32-33: the named Lazard series of the generic structure is both the lower and reversed upper central series.
- **Corollary 4.42, pp. 33-34:** explicitly takes the theory of the group reduct in `{multiplication, inverse, 1}` and states that it is the model companion of the theory of c-nilpotent groups of exponent p. Its proof defines the series predicates both existentially and universally in the Lie reduct and then transfers through Lazard. Consequently, this is genuinely a pure group result; the manuscript has not confused expanded-language amalgamation with pure-language model completeness.
- Remark 4.43, p. 34: reports that Saracino-Wood give explicit axioms for the model companion of class-2 groups of exponent m, for m in N. The subsequent displayed simpler axioms concern the odd-prime special case. These are distinct scopes; one should not restrict the historical arbitrary-finite-exponent result just because the displayed special axioms use F_p.
- Introduction, pp. 2-3: credits Maier 1989 with exponent-p/class-c amalgamation for p > c, and explains how strong amalgams for the corresponding filtered Lie algebras follow from Maier by Lazard. This supports the manuscript's cautious wording “follows from Maier's amalgamation results,” rather than falsely saying Maier directly stated Corollary 4.42.
- Publication metadata is verified at the [author's university repository](https://fount.aucegypt.edu/faculty_journal_articles/6073/) and [coauthor's research page](https://www.nramseymath.com/research): Journal of Algebra **662** (2025), 640-701, DOI [10.1016/j.jalgebra.2024.08.012](https://doi.org/10.1016/j.jalgebra.2024.08.012). The manuscript bibliography matches.
- **Version limit:** publisher full text could not be retrieved. Therefore Corollary **4.42 is directly verified in arXiv v3**, but persistence of exactly that numbering in the final published 61-page article is not verified here. This is an unresolved bibliographic locator check, not evidence that the theorem or number is wrong.
- Visually inspected the complete rendered PDF pp. 33-34 as well as extracted text of pp. 2-3 and 32-34.

### Saracino 1976

- [Original publisher page and abstract](https://link.springer.com/article/10.1007/BF02757003), *Existentially complete nilpotent groups*, Israel Journal of Mathematics **25** (1976), 241-248.
- The abstract defines K_n as the theory of nilpotent groups of class at most n and K_n^+ as its torsion-free version. It states that **both have no model companion for n >= 2**.
- This directly verifies every hypothesis and conclusion in v8 line 139, including the attribution of the torsion-free result to 1976. It is unnecessary to replace the citation by Saracino 1978 merely because that later article's title specifically mentions torsion-free groups.
- As a cross-check, Saracino's [1978 original follow-up publisher extract](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/3B94D038780BFDC72F29B7DC0D96E5E8/S0022481200049951a.pdf/existentially_complete_torsionfree_nilpotent_groups.pdf) expressly attributes both nonexistence assertions to [6], the 1976 paper.
- Full-text theorem numbering and proof pages within 241-248 were not verified. The bibliography's year, title, author, volume, pages and DOI match the publisher.

### Saracino 1974

- Cited article: [DOI](https://doi.org/10.1090/S0002-9947-1974-0342391-5), *Wreath products and existentially complete solvable groups*, Trans. AMS **197** (1974), 327-339.
- The article's AMS PDF/page and JSTOR original scan could not be read because the public retrieval attempts returned access errors. No original article theorem number has been verified.
- Primary-source corroboration: the author's announcement **74T-E36**, *On existentially complete nilpotent groups. Preliminary report*, [Notices AMS, April 1974 issue](https://www.ams.org/journals/notices/197404/197404FullIssue.pdf), printed **A-379**. Search-index extraction of that primary document states the already-known absence of a model companion for each solvable-length bound <= n, n >= 2. This is an author announcement, but is not a substitute for a complete read of the cited article.
- Suggested precision change to line 138, independently of whether the eventual full-text check changes anything: “Saracino proved that, for every n >= 2, the theory of solvable groups of derived length at most n has no model companion.” This avoids reading “fixed derived length” as exactly n or “at least 2” as the class of all nonabelian solvable groups. It is a wording improvement, not an identified false claim.

### Saracino-Wood 1979

- [Original DOI](https://doi.org/10.1016/0021-8693(79)90199-6), *Periodic existentially closed nilpotent groups*, J. Algebra **58** (1979), no. 1, 189-207.
- Original full text could not be obtained. Elsevier's public XML endpoint returned only article metadata, not theorem statements; this is saved as `references/audit-artifacts/t3-model-companion/2026-09-23/v8-reference-review/saracino_wood1979.xml` and `.txt`.
- Direct corroboration in another original research paper: d'Elbee et al., Remark 4.43, p. 34, as above, explicitly attributes the arbitrary finite exponent result to this paper. That is secondary evidence **for the historical 1979 assertion**, even though d'Elbee et al. is itself a primary source for its own theorems.
- Do not mark the 1979 original theorem/page check complete on this evidence. In particular, no exact theorem number for the arbitrary finite exponent assertion has been certified here.

### Maier 1989

- [Original DOI](https://doi.org/10.1016/0021-8693(89)90253-6), *On nilpotent groups of exponent p*, J. Algebra **127** (1989), no. 2, 279-289.
- Original full text could not be obtained. Elsevier's public XML endpoint returned only metadata, saved as `references/audit-artifacts/t3-model-companion/2026-09-23/v8-reference-review/maier1989.xml` and `.txt`.
- d'Elbee et al., Introduction pp. 2-3, directly credits precisely exponent p and nilpotency bound c with p > c. Their Corollary 4.42 independently verifies the resulting pure-group model companion assertion. The direct historical theorem-level attribution still needs Maier's original text.
- Optional precision change to line 144: “For prime p and c < p, the theory of groups of exponent p and nilpotency class at most c has a model companion [dEMRS, Cor. 4.42]; its construction rests on the amalgamation results of Maier [Mai1989].” This places the checked direct model-theoretic theorem first while preserving algebraic provenance. The existing “follows from” wording is already reasonable.

## Review boundary

- No modifications to the mathematical source or manuscript.
- No Lean build/check runs: this subtask is reference-statement verification only.
- No verified counterexample or false attribution in this cluster.
- Pending original-source checks: Saracino 1974 article theorem, Saracino-Wood 1979 arbitrary-exponent theorem, Maier 1989 theorem, and d'Elbee et al. final published numbering.
- The full-text evidence available supports the manuscript's use of the **ordinary group language**, not merely the auxiliary language naming a Lazard series.
