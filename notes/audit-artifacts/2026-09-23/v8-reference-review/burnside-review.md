# v8 bibliography review: Levi-van der Waerden and Ivanov

Review date: 2026-09-23. Manuscript checked: `T3_modelcompanion_v8.tex`, SHA-256
`9546045ccd5cb0170ac54fe1485d356765400ed938c57442da558c41c51fa38c`.
Read-only manuscript review; no TeX or Lean changes.

## Verdict

The mathematical content attributed to Levi and van der Waerden is accurate,
including the commutator convention and all indices and signs in the normal
form. Ivanov's theorem supports the sufficiently-large-prime claim, but line 183
should specify rank at least two: rank-one free Burnside groups are finite.
Both bibliography records have the correct authors, title, year, volume, and
pages. No serious mathematical attribution error found in these two references.

## Levi and van der Waerden (1933)

Primary source: F. Levi and B. L. van der Waerden, *Über eine besondere Klasse
von Gruppen*, Abh. Math. Sem. Univ. Hamburg **9** (1933), 154-158.
[Publisher metadata](https://link.springer.com/article/10.1007/BF02940639).
The publisher gives December 1933, volume 9, pages 154-158, and the DOI in v8.

Local published PDF:
`references/publications/levi-van-der-waerden-1933-besondere-klasse-von-gruppen-published.pdf`.
Reviewed complete printed pp. 155-157 using the existing page images. OCR was
used only for navigation; several OCR signs and exponents are wrong.

| Manuscript location | Primary-source locator | Finding |
| --- | --- | --- |
| 167: every exponent-three group has class at most three; bound attained | p. 155, eqs. (5)-(6), following paragraph; pp. 156-157, Satz 1 | Correct. The second commutators are central. The free group on three generators has an independent triple-commutator coordinate, so class three occurs. |
| 231-232: binary commutator and left-associated iterated commutator | p. 155, (5) and (6) | Exact match: `(i,k)=iki^{-1}k^{-1}` and `(i,j,k)=((i,j),k)`. No convention reversal or inverse correction is needed. |
| 609-617 / Fact 2.27: order and unique normal form | p. 156, (8); Satz 1 beginning p. 156 and ending p. 157 | Exact match after shifting indices from `1,...,n` to `0,...,r-1`. Order is `3^(r + binom(r,2) + binom(r,3))`. Coordinates range over `0,1,2`, equivalently F3. |
| 613-614: `[x_i,x_j]` and `[x_i,x_j,x_k]` for `i<j<k` | p. 155 definitions; p. 156 normal form (8) | Exact match. Pair factors commute; triple factors are central, so the unspecified ordering within either product does not affect the expression. |
| 619-629: extension to infinite rank | The published theorem is finite rank | Correct derived extension, not a literal assertion of Satz 1. A word uses finitely many generators; inclusion of the finite generated free subobject splits by killing other generators. This gives both existence and uniqueness from finite rank. The manuscript already places this in a separate remark. |
| 1606-1611: bibliography | Publisher metadata and PDF title | Correct. |

The class bound in line 167 has no hidden finite-generation restriction: the
source identities hold for arbitrary elements, or alternatively any quadruple
lies in a finitely generated subgroup. Sharpness follows specifically from
the nonzero `(1,2,3)` coordinate in rank three.

Optional precision only: give the normal-form citation as
`\cite[Satz 1, pp.~156--157]{LeviVanDerWaerden1933}`.

## Ivanov (1992)

Primary source: S. V. Ivanov, *On the Burnside problem on periodic groups*,
Bull. Amer. Math. Soc. (N.S.) **27** (1992), no. 2, 257-260.

- [Author's arXiv record](https://arxiv.org/abs/math/9210221).
- [Primary text, Theorem A](https://arxiv.org/html/math/9210221v1).
- [Journal issue metadata](https://www.ams.org/bull/1992-27-02/).
- Journal DOI: `10.1090/S0273-0979-1992-00305-1`.

The AMS-hosted PDF returned HTTP 403. The author's arXiv PDF was obtained and
its complete page 2 was visually inspected. It reproduces the article with
local page numbers 1-4 and a first-page header giving the published issue and
257-260 pagination. Theorem A occurs on arXiv p. 2; this is the source locator
verified visually, rather than an inferred printed-page locator.

Saved PDF: `references/audit-artifacts/t3-model-companion/2026-09-23/v8-reference-review/sources/ivanov-1992-arxiv.pdf`, SHA-256
`873cfd389b1669bf7c4262e2b2effbde6b64e716b7f96727a6734f4e69464e08`.
Saved text: `references/audit-artifacts/t3-model-companion/2026-09-23/v8-reference-review/sources/ivanov-1992-arxiv.txt`.

Theorem A assumes `m>1` and `n>=2^48`; part (a) says `B(m,n)` is infinite.
It therefore implies the claim needed in v8 for every sufficiently large prime
and every finite rank at least two. No parity or divisibility condition has
been omitted from the cited 1992 statement.

**Minor mathematical wording correction (line 183).** The unqualified phrase
"The free Burnside groups are infinite for such primes" does not state the
rank restriction. Since `B(1,p)` is cyclic of order p, this sentence should
either specify rank at least two or simply use rank two, which is all that
is needed to refute local finiteness. Suggested wording:

```tex
The free Burnside groups $B(2,p)$ are infinite for all sufficiently large
primes $p$ \cite[Theorem~A(a)]{Ivanov1992}, so this shows the conjecture
for all sufficiently large primes.
```

If retaining the existing relation to the previous sentence, an equally small
edit is "The free Burnside groups of rank at least two are infinite for such
primes". No change to the conjecture or argument is needed.

The 1992 note is a research announcement with remarks on proofs; the complete
proof paper is Ivanov (1994), *The free Burnside groups of sufficiently large
exponents*, Int. J. Algebra Comput. **4** (1-2), 1-308. This is a separate work,
not a bibliographical reason to replace the 1992 year in the existing entry.
The local 1994 published PDF, p. 2, was also visually checked: Theorem A has
`m>1`, `n>=2^48`, and `n` odd or divisible by `2^9`, and part (a) asserts
infiniteness. Large prime exponents satisfy its odd alternative. Adding the
1994 full proof citation could improve provenance but is not required to fix
the mathematical claim in v8.

The 1992 reference supports only the group-theoretic infiniteness assertion.
The separate claimed model-companion nonexistence result in lines 182 and 184
is explicitly announced by the manuscript authors and is not a result in
Ivanov's paper; it is outside this citation check.
