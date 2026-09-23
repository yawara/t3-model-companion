# Independent re-review: Saracino 1974 and v8 source holdings

Review date: 2026-09-24. Manuscript: `T3_modelcompanion_v8.tex`, SHA-256
`9546045ccd5cb0170ac54fe1485d356765400ed938c57442da558c41c51fa38c`.
No existing TeX, Lean, or audit file was edited.

## Saracino 1974: verdict

Theorem 1 directly supports the intended nonexistence assertion in v8 line
138. The precise original statement concerns **derived length at most n,
for every fixed n >= 2**. The sentence in v8 is mathematically defensible,
but replacing "fixed derived length at least 2" with an explicit upper bound
would make it match the cited theorem and eliminate a possible exact-length
reading. This is a precision improvement, not a false theorem attribution.

Primary source: D. Saracino, *Wreath products and existentially complete
solvable groups*, Transactions of the American Mathematical Society **197**
(1974), 327-339, [DOI](https://doi.org/10.1090/S0002-9947-1974-0342391-5).

Local original journal PDF:
`references/publications/saracino-1974-wreath-products-existentially-complete-solvable-groups-published.pdf`,
SHA-256 `c21795385728a024229f52a718adb777a7e65b77e0c5130ea23e5ca26e5e3b9e`.
PDF page k corresponds to printed page 326+k. The locally registered file
was obtained from an Internet Archive capture of the AMS publisher PDF;
the edition is the published article.

### Directly checked locators

- **p. 327, abstract:** for every fixed n >= 2, the theory of groups solvable
  of length <= n has no model companion.
- **p. 327, introduction:** T_n is defined as the theory of groups solvable
  of length <= n; n starts at 1, so T_1 is abelian groups and T_2 metabelian
  groups.
- **p. 327, Theorem 1:** for every n >= 2, T_n has no model companion.
- **pp. 328-329, section 1:** the group language has multiplication, inverse,
  and identity. Length <= n means G^(n) = {1}. T_n is the group theory plus
  the universal identity saying every nth derived commutator is trivial.
  This explicitly includes groups of smaller derived length.
- **pp. 330-332, section 2:** the proof constructs an ultrapower of an
  existentially complete model of T_n which is not existentially complete.
  The scope is the universal upper-bound theory; it is not restricted to
  finite groups, finitely generated groups, or a fixed exponent.

The full pages 327-329 and 331 were checked visually, not just by OCR. In the
text extraction, several occurrences of <= or >= incorrectly become < or >;
the page images unambiguously show the non-strict inequalities.
The proof on pp. 330-332 was read in the extraction to confirm its scope;
this review does not claim a fresh line-by-line proof audit of the complete
article.

Suggested replacement for v8 line 138:

```tex
Saracino proved that, for every $n\geq2$, the theory of groups of derived
length at most $n$ has no model companion~\cite[Theorem~1]{Saracino1974}.
```

### Exact length versus length at most n

The source theorem itself is about length **at most** n. However, if v8's
"fixed derived length" is read as **exactly** n, nonexistence still follows
by a short additional argument. This is an inference, not the literal
wording of Theorem 1:

1. Choose a solvable group H_n of derived length exactly n. Such groups also
   occur in the source's iterated-wreath construction in the proof of
   Proposition 3, p. 331: length is at most n and an (n-1)st derived
   commutator has a prescribed prime order, so length is not at most n-1.
2. Every G of derived length <= n embeds into G x H_n, whose derived length
   is exactly n. Conversely, every length-exactly-n group has length <= n.
3. The two theories are mutually model-consistent (equivalently they have
   the same universal consequences). A model companion of either would
   therefore be a model companion of the other. Theorem 1 rules this out.

Thus there is no counterexample arising merely from the exact-versus-bounded
reading. Nevertheless, citing the actual upper-bound theorem is clearer and
avoids requiring this extra argument.

Bibliographic metadata in v8 lines 1620-1625 matches the journal title page,
author, volume, year, pages, and DOI. The received date 1973 on p. 327 does
not change the publication year 1974.

## Inventory of the 13 v8 bibliography entries

This inventory checks files in `references/` and the 2026-09-23 reference
audit directory, plus the corresponding MANIFEST entries. It classifies
source availability, not the fidelity verdict for each statement. In
particular, possessing the full Eklof-Fischer article does not mean that
the v8 attribution to it is correct.

| Citation | Available source | Boundary |
| --- | --- | --- |
| CK1990 | Google Books public third-edition excerpts, saved as JSON in the audit | Example 3.5.16 and p. 199 directly checked; no complete book PDF held here |
| dEMRS2025 | Complete author PDF, arXiv 2310.17595v3, `demrs2025.pdf` in the audit | Final Journal of Algebra PDF not held; final published Corollary 4.42 numbering remains to be checked |
| EF1972 | Complete published PDF in `references/publications/`; MANIFEST section 19 | Full source held |
| ES1971 | Complete published PDF in `references/publications/`; MANIFEST section 18 | Full source held |
| FK2025 | Complete original preprint PDF, arXiv 2512.09414v2, audit `sources/` | v8 cites a preprint; this is the cited type of source, not an absent-journal-version defect |
| HKTY2023 | Complete original preprint PDF, arXiv 2312.08988v2, audit `sources/` | Same distinction as FK2025 |
| Iva1992 | Complete author PDF, arXiv math/9210221, audit `sources/ivanov-1992-arxiv.pdf` | Original AMS typeset PDF not held; Theorem A verified in author text |
| LW1933 | Complete published PDF in `references/publications/`; MANIFEST section 12 | Full source held |
| Mai1989 | Complete published PDF in `references/publications/`; MANIFEST section 17 | Full source held |
| Sar1974 | Complete published PDF in `references/publications/`; MANIFEST section 20 | Full source held and independently checked in this note |
| Sar1976 | Original publisher abstract directly checked in earlier audit | Full article PDF not held; exact conclusion is in the primary abstract |
| SW1979 | Complete published PDF in `references/publications/`; MANIFEST section 16 | Full source held |
| Tak2022 | Complete RIMS published PDF in `references/publications/`; MANIFEST section 21 | Full source held; image-only PDF, inspected via page images |

Counts: **7 published full texts, 4 author/preprint full texts, and 2 sources
available only as primary excerpts/abstracts**. Among already published works,
the complete publication versions not held in these paths are CK1990,
dEMRS2025, Iva1992, and Sar1976. Of those four, dEMRS2025 and Iva1992 have
complete author text available; CK1990 and Sar1976 have narrower direct
evidence. The original preprint entries FK2025 and HKTY2023 should not be
presented as missing publisher PDFs.

The 2026-09-23 component notes predate acquisition of several published PDFs.
Their old "full text not obtained" statements for Sar1974, SW1979, Mai1989,
EF1972, and ES1971 are superseded by the actual current holdings and by the
updated consolidated audit. No old audit file was modified in this task.
