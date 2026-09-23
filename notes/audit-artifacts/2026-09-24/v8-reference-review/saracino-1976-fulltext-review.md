# Saracino 1976: supplied full-text review

Review date: 2026-09-24. Source: the user-supplied
`references/saracino1976.pdf`, SHA-256
`584f4fed02a81d9e88de1cce1862fa31464c0620c3c8054d2eb73e5c7e7fab7b`.
The supplied file was preserved in place without editing or re-exporting it.

## Verdict

**The two nonexistence assertions at v8 line 139 agree exactly with the
published article.** The previous abstract-only boundary is resolved.

- **Theorem 1, printed p.241 / PDF p.1:** for every integer n >= 2, the
  theory of groups nilpotent of class at most n has no model companion.
- **Theorem 2, printed p.242 / PDF p.2:** the same nonexistence result holds
  for the theory of torsion-free groups nilpotent of class at most n.
- The lower bound is **>= 2**, not > 2. Both statements are visible on the
  original page images, despite damaged inequality symbols in the text layer.

Bibliography: D. Saracino, *Existentially complete nilpotent groups*,
Israel Journal of Mathematics **25** (1976), 241–248,
[DOI](https://doi.org/10.1007/BF02757003).
The supplied PDF contains all eight published pages, with the journal
header, title, author, and references. The edition is the published article;
the exact website from which the user obtained this file was not supplied.

## Hypotheses, language, and proof scope

The original pp.242–243 explicitly use the ordinary group language
(multiplication, inverse, identity) and define K_n by the group axioms and
the identity making every (n+1)-fold commutator trivial. Consequently the
class bound is **at most n**, not exactly n. No finite-generation, exponent,
countability, or extra-predicate assumption is imposed on the target theory.

The source uses [a,b] = a^-1 b^-1 a b, unlike v8's a b a^-1 b^-1.
This changes individual commutator formulas but not the lower central
subgroups, the nilpotency-class bound, or the nonexistence theorem being
cited. No source commutator identity is being transplanted into v8 here.

For Theorem 1, pp.243–244 construct an ultrapower G* of an e.c. model
containing b,c with C(b) contained in C(c), and a same-class extension
realizing `exists x, xb=bx and xc != cx`. That existential formula is
not realized in G*, so the e.c. models are not closed under ultrapowers
and cannot form an elementary class. Proposition 3 constructs the extension
through a free product followed by the nilpotency and central quotients.

For Theorem 2, pp.244–245 adapt this argument in Propositions 4–6.
The quotient by the torsion subgroup gives a torsion-free extension.
The strengthened independence condition and the centrality of [c,a]
ensure that the required failure to commute survives this quotient.
The centrality assumption in Proposition 6 is verified for the constructed
ultrapower elements at the end of p.245; it is not an omitted hypothesis
on the theories in Theorem 2 or v8.

Theorem 3 (p.242), about finite and infinite generic models, is a stronger
additional result for K_n; the article explicitly warns that its proof
does not carry over to the torsion-free case. v8 does not make that
extension and instead correctly cites the separate nonexistence result.

## Evidence and suggested locator

All eight pages were read as extracted text; the complete relevant pages
241–245 were also inspected visually at 180 DPI and retained under
`references/rendered-pages/saracino-1976/`. The text layer is a locating aid,
not authoritative for inequalities and mathematical notation.

The citation can be made more precise as
`\cite[Theorems~1 and~2]{Saracino1976}`. No mathematical correction is
needed at line 139. The manuscript was not edited; its SHA-256 remains
`9546045ccd5cb0170ac54fe1485d356765400ed938c57442da558c41c51fa38c`.

This review checks correspondence and the relevant proof's scope; it does
not claim a new formal verification of the complete source article.
