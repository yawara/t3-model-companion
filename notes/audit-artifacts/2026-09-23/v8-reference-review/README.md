# Reference-review evidence storage

External source PDFs, page images, extracts and source metadata are stored in
`references/audit-artifacts/t3-model-companion/2026-09-23/v8-reference-review/`
in a separate literature archive. The T3 repository ignores `/references/` and tracks
only the authored review notes and inventories. The exact relocation map and
unchanged hashes are recorded in
`notes/audit-artifacts/2026-09-24/v8-reference-review/evidence-storage.json`.

---

# v8 reference review: consolidated report

Review date: 2026-09-23. Manuscript: `T3_modelcompanion_v8.tex`, SHA-256
`9546045ccd5cb0170ac54fe1485d356765400ed938c57442da558c41c51fa38c`.
Read-only review. No TeX or Lean changes were made.

Updated 2026-09-24: the user supplied the publisher PDFs of Eklof-Sabbagh
1971, Eklof-Fischer 1972, Saracino-Wood 1979 and Maier 1989. They are
registered in `references/` (MANIFEST sections 16-21, together with the AMS
copy of Saracino 1974 and the RIMS copy of Takeuchi 2022), and every statement
below was re-checked against them.

Question reviewed: does every statement in v8 that is attributed to a cited
reference agree with what that reference actually proves? Bibliographic
metadata (authors, title, venue, volume, pages, year, DOI/arXiv id) was checked
as well.

The bibliography has 13 entries. Twelve are cited in active text (13 `\cite`
commands, lines 133-609); `EklofSabbagh1971` is cited only inside the disabled
block `\if0` (line 1464) ... `\fi` (line 1547). See `citation-inventory.json`.

The earlier partial notes in this directory (`burnside-review.md`,
`chang-keisler-review.md`, `model-complete-review.md`, `nilpotent-review.md`)
are superseded by this file where they list pending checks; the checks they left open for Saracino 1974, Saracino-Wood 1979, Maier 1989,
Eklof-Fischer 1972 and Eklof-Sabbagh 1971 were completed against the original
full texts (see Evidence).

## Summary

| v8 line | Reference | Statement in v8 | Verdict |
| --- | --- | --- | --- |
| 133 | EF1972 | every inductive theory of abelian groups with JEP has a model companion | **Not supported by the cited source.** The 1972 Ann. Math. Logic paper contains no result on model companions, inductive theories, or JEP. Nearest published result: Eklof, JSL 37 (1972): complete inductive theories of abelian groups are exactly the model-complete ones. |
| 136 | CK90 | theory of groups has no model companion, Example 3.5.16 | Correct (3rd ed., p. 199). Original result: Eklof-Sabbagh 1971, Theorem 7.17. |
| 137 | Tak2022 | torsion-free groups have no model companion | Correct (Theorem 17, p. 5). |
| 138 | Sar1974 | non-existence for solvable groups of fixed derived length >= 2 | Correct (Theorem 1: for every n >= 2, solvable of length <= n). Wording could be made precise. |
| 139 | Sar1976 | for every c >= 2 neither nilpotent class <= c nor its torsion-free version has a model companion | Correct (publisher abstract, verbatim). |
| 143 | SW1979 | fixed finite exponent, class <= 2: model companion exists | Correct (Theorem 3.9, p. 198: for 2 <= m < infinity, T^m, the theory of nilpotent class 2 groups of exponent m, has an aleph_0-categorical model companion). Verified on the publisher PDF. |
| 144 | Mai1989 | for prime p and class <= c < p, existence follows from Maier's amalgamation results | Correct. Maier proves it himself: Theorem 3.5 (aleph_0-categorical model companion). Note the class does **not** have the amalgamation property; Theorem 2.1 characterises the amalgamation bases. |
| 144 | dEMRS2025 | see also Corollary 4.42 | Correct in arXiv v3 (pp. 33-34). Numbering in the published version (J. Algebra 662) could not be checked. |
| 147 | HKTY2023, FK2025 | model-complete pure group theories for some semisimple algebraic groups and Heisenberg groups over model-complete fields | Correct (HKTY v2 Theorem 3.3; FK v2 Theorem 3.6). |
| 167, 609 | LW1933 | exponent 3 implies class <= 3, attained; order 3^{r+C(r,2)+C(r,3)}; normal form | Correct (pp. 155-157, Satz 1, formula (8)); commutator conventions agree. |
| 172 | Tak2022 | Burnside connection noted by the third author | Correct (p. 2, last paragraph of Section 1). |
| 183 | Iva1992 | free Burnside groups infinite for all large primes | Correct (Theorem A: m > 1, n >= 2^48). Rank >= 2 should be stated. |
| 1502 (disabled) | ES1971 | theory of abelian groups has a model companion | Correct (Theorem 2.4). Entry is otherwise uncited in the active text. |

Bibliographic metadata: all 13 entries agree with Crossref/arXiv/RIMS records
(authors, titles, volumes, issues, pages, years, DOIs, arXiv ids). Details in
the section "Bibliography metadata" below.

## Findings that need an edit

### 1. Line 133: Eklof-Fischer 1972 does not contain the cited theorem

v8 reads: "More generally, Eklof and Fischer proved that every inductive
theory of abelian groups with the joint embedding property has a model
companion~\cite{EklofFischer1972}."

The complete original text (57 pages, Ann. Math. Logic 4 (1972) 115-171;
publisher PDF `references/publications/eklof-fischer-1972-elementary-theory-of-abelian-groups-published.pdf`,
first read in an Internet Archive copy of the CORE mirror, which agrees) was read. Its sections are:
Introduction; 0 Preliminaries; 1 The structure of saturated abelian groups;
2 Elementary embeddings and decidability; 3 The existence of saturated abelian
groups; 4 Elimination of quantifiers; 5 Modules over a Dedekind domain; Added
in proof. The words "model companion", "model completion", "inductive",
"joint embedding" and "existentially closed" do not occur (checked with
OCR-tolerant patterns). The only mention of model completeness is the "Added in
proof" remark about Kargapolov's erroneous use of Robinson's test (p. 170).
The introduction lists the paper's results (Szmielew invariants, saturated
groups, decidability, quantifier elimination in an extended language, Dedekind
domains); none concerns model companions.

The nearest published result is in the companion paper P. C. Eklof, *Some model
theory of abelian groups*, J. Symbolic Logic 37 (1972), no. 2, 335-342,
doi:10.2307/2272976, whose abstract states: "we characterize the inductive
complete theories of abelian groups and prove that they are exactly the
model-complete theories." That is a statement about **complete** theories and
does not by itself give the sentence in v8 (an incomplete inductive theory
with JEP). No source proving the JEP version was found during this review
(zbMATH, Crossref, OpenAlex and web search were consulted).

Suggested resolution, in order of preference:

1. Replace the sentence by the statement that is actually in the literature,
   with the correct reference:

   ```tex
   More generally, Eklof proved that a complete theory of abelian groups is
   model complete if and only if it is inductive~\cite{Eklof1972}.
   ```

   and add the bibliography entry

   ```tex
   \bibitem[Ekl1972]{Eklof1972}
   P.~C.~Eklof,
   \emph{Some model theory of abelian groups},
   J. Symbolic Logic \textbf{37} (1972), no.~2, 335--342.
   \href{https://doi.org/10.2307/2272976}{doi:10.2307/2272976}.
   ```

   The Eklof-Fischer entry can then be dropped unless it is used elsewhere.
2. Keep the JEP sentence only if a proof or a reference that proves it is
   supplied. As written, the attribution is incorrect.

### 2. `EklofSabbagh1971` is in the bibliography but uncited in the active text

Its only citation (line 1502) is inside `\if0 ... \fi`. With a manual
`thebibliography`, the entry is still printed. Either cite it where the
model companion of abelian groups is invoked (line 131 or line 136, since
Example 3.5.16 of Chang-Keisler is Eklof-Sabbagh's Theorem 7.17), or remove
the entry. Suggested citation for line 136:

```tex
The theory of all groups has no model companion
\cite[Theorem~7.17]{EklofSabbagh1971}; see also
\cite[Example~3.5.16]{ChangKeisler1990}.
```

### 3. Line 183: rank restriction

"The free Burnside groups are infinite for such primes" is false for rank one.
Ivanov's Theorem A assumes m > 1. Suggested:

```tex
The free Burnside groups of rank at least two are infinite for such
primes \cite[Theorem~A]{Ivanov1992}, ...
```

## Precision improvements (optional, no error)

- Line 138: Saracino 1974, Theorem 1 is "for any n >= 2, the theory of groups
  solvable of length <= n has no model companion." Suggested wording:
  "Saracino proved that, for every n >= 2, the theory of solvable groups of
  derived length at most n has no model companion \cite[Theorem~1]{Saracino1974}."
- Line 144: cite the theorem: `\cite[Theorem~3.5]{Maier1989}`. Maier's class
  K = N_c \cap B^p (p prime, c < p) does not have the amalgamation property;
  Theorem 1.2 gives the realizability criterion (coupled central series),
  Theorem 2.1 shows that D in K is an amalgamation base iff its upper and lower
  central series coincide, and Theorem 3.5 derives from these a unique
  countable existentially closed group and an aleph_0-categorical model
  companion. The v8 wording "follows from Maier's amalgamation results" is
  therefore accurate, but the reader should not infer that K has AP.
- Line 136: `\cite[Example~3.5.16, p.~199]{ChangKeisler1990}`.
- Line 609: `\cite[Satz~1, pp.~156--157]{LeviVanDerWaerden1933}`.
- Line 147: "some semisimple algebraic groups" is an understatement of HKTY
  Theorem 3.3 (all split semisimple algebraic groups G over a model-complete
  field K: G(K) and G(K)' are model complete). FK Theorem 3.6 is an
  equivalence: H(K) is model complete iff K is.
- HKTY and FK are cited as unversioned preprints; the theorem numbers above
  refer to v2 (HKTY v2: 2 March 2025; FK v2: 8 February 2026). Adding the
  version or date would make the locators stable.
- dEMRS: "Corollary 4.42" is verified in arXiv:2310.17595v3 (21 June 2024,
  45 pp.); the journal version (J. Algebra 662 (2025) 640-701) is 62 pages
  and its numbering was not checked (publisher and the AUC repository copy
  both returned HTTP 403).

## Per-reference verification details

### Saracino 1974 (line 138)

Full text obtained (Trans. AMS 197 (1974) 327-339, Internet Archive capture of
the AMS journal PDF, registered as
`references/publications/saracino-1974-wreath-products-existentially-complete-solvable-groups-published.pdf`;
Theorem 1 checked on the rendered p. 327). Abstract: "We show that for
any fixed n >= 2 the theory of groups solvable of length <= n has no model
companion." Theorem 1 (p. 327): "For any n >= 2, T_n has no model companion",
where T_n is the theory of groups solvable of length <= n. Footnote (2),
p. 338: "The author has shown that for fixed c >= 2 the theory of groups
nilpotent of class <= c has no model companion." Matches v8.

### Saracino 1976 (line 139)

Publisher abstract (Springer, Israel J. Math. 25 (1976) 241-248): "if n >= 2
then neither K_n nor K_n^+ has a model companion", with K_n the theory of
groups nilpotent of class at most n and K_n^+ its torsion-free version.
Matches v8 exactly, including the torsion-free case. dEMRS (introduction,
p. 2) attributes both non-existence results to this paper as well. Full text
not obtained (closed access).

### Saracino-Wood 1979 (line 143)

Publisher PDF supplied by the user (J. Algebra 58 (1979) 189-207;
`references/publications/saracino-wood-1979-periodic-existentially-closed-nilpotent-groups-published.pdf`;
PDF p. k is printed p. 188+k). p. 189: T is the theory of nilpotent class 2
groups and T^m = T u {forall x (x^m = 1)} is "the theory of nilpotent class 2
groups of exponent m". Introduction, p. 190: "For the case of bounded
exponent, we show that T^m has an aleph_0-categorical model companion."
Theorem 3.9, p. 198 (rendered page checked): "For 2 <= m < infinity, T^m has
an aleph_0-categorical model companion, hat T^m." The proof (pp. 198-200)
lists axiom groups I-III for every prime power dividing m, with separate
axioms for p = 2, and assembles hat T^m from them, so even exponents are
included. This is exactly v8 line 143. The secondary confirmations recorded
before the file arrived (Maier 1989, p. 280, citing "[12, Theorem 3.9]";
zbMATH review Zbl 0673.03024, item (iii); dEMRS Remark 4.43) agree. Renders:
`references/rendered-pages/saracino-wood-1979/`.

### Maier 1989 (line 144)

Full text: publisher PDF supplied by the user,
`references/publications/maier-1989-nilpotent-groups-of-exponent-p-published.pdf`
(J. Algebra 127 (1989) 279-289; PDF p. k is printed p. 278+k; Theorem 3.5
checked on the rendered page). An Internet Archive copy of the CORE mirror
read first agrees. Relevant statements:

- p. 279: K = N_c \cap B^p, p a prime greater than c.
- p. 280: "We also show that K and K' do have model companions but N_c^n,
  c >= 2, does not."
- Theorem 1.2 (c < p): an amalgam D <= A, B in K can be realized in K iff there
  exist coupled central series of length c in A and B.
- Theorem 2.1 (c < p): D in K is a (strong) amalgamation base in K iff
  D_i = Z_{c+1-i}(D) for 1 <= i <= c.
- Theorem 3.5 (c < p): "There exists a unique countable existentially closed
  group in K, and K has an aleph_0-categorical model companion." The proof
  writes down the axioms (I)-(III).

Matches v8 line 144. The disabled line 1476 ("obtained from Maier's
amalgamation results") is likewise consistent.

### d'Elbee-Mueller-Ramsey-Siniora 2025 (line 144)

arXiv:2310.17595v3, pp. 33-34, rendered pages `references/audit-artifacts/t3-model-companion/2026-09-23/v8-reference-review/demrs-page-33.png`,
`references/audit-artifacts/t3-model-companion/2026-09-23/v8-reference-review/demrs-page-34.png`: "Corollary 4.42. Let T^grp_{c,p} be the theory of
G_{c,p} in the language of groups {., ^{-1}, 1}. Then T^grp_{c,p} is the
model-companion of the theory of c-nilpotent groups of exponent p." G_{c,p}
is the Fraisse limit of the class of finite Lazard groups of exponent p and
class c, defined for c < p (pp. 32-33); the standing hypothesis is an odd
prime p > c (abstract; Facts 2.13-2.14). The reduct to the pure group language
is explicit, so the "see also" citation is appropriate. Journal numbering not
verified (see above).

### Eklof-Sabbagh 1971 (line 1502, disabled; origin of line 136)

Full text: publisher PDF supplied by the user,
`references/publications/eklof-sabbagh-1971-model-completions-and-modules-published.pdf`
(Ann. Math. Logic 2 (1971) 251-295; PDF p. k is printed p. 250+k; Theorems
2.4 and 7.17 checked on the rendered pages). Theorem 2.4 (p. 256):
K*, the theory of divisible abelian groups with infinitely many elements of
each prime order, is the model companion (hence model completion) of the
theory of abelian groups. Theorem 7.17 (p. 291): "The theory T_1 of groups
has no model-companion." Chang-Keisler's historical note (3rd ed., p. 609)
credits Example 3.5.16 to this paper.

### Eklof-Fischer 1972 (line 133)

See Finding 1. Full text: publisher PDF supplied by the user,
`references/publications/eklof-fischer-1972-elementary-theory-of-abelian-groups-published.pdf`
(PDF p. k is printed p. 114+k). The keyword search was repeated on this
file with the same result: no occurrence of "companion", "inductive",
"joint embedding", "forcing" or "generic" on any of the 57 pages; the only
"model-completeness" occurrence is the Added-in-proof remark on p. 170. The
summary of results on p. 116 (rendered page checked) lists no such theorem.

### Chang-Keisler 1990 (line 136)

Google Books in-volume search of the 1990 third edition (id uiHq0EmaFp0C,
Elsevier 1990, Studies in Logic 73, 649 pp.): "EXAMPLE 3.5.16. The theory of
groups has no model companion." on p. 199; historical notes p. 609: "3.5.16:
Eklof and Sabbagh (1971)". Raw responses in `sources/chang-keisler-*.json`.

### Takeuchi 2022 (lines 137, 172)

RIMS Kokyuroku 2218 (2022), 79-84, contents page
`https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/2218.html`
(entry 10, pdf `2218-10.pdf`); registered copy
`references/publications/takeuchi-2022-model-companions-of-some-classes-of-groups-published.pdf`
(image-only scan; page images `references/audit-artifacts/t3-model-companion/2026-09-23/v8-reference-review/sources/takeuchi-1.png` ... `takeuchi-6.png`
and renders in `references/rendered-pages/takeuchi-2022/`). Abstract: "we
prove that torsion free groups has no model companion". Theorem 17 (p. 5):
the theory of groups and the theory of torsion-free groups have no model
companion. Page 2: "It is also very interesting that discussing the existence
of model companion of exponent n groups with the connection to the Burnside
problem, however, this topic will appear in another opportunity in the future
work." Both v8 statements match.

### Hoffmann-Kowalski-Tran-Ye (line 147)

arXiv:2312.08988v2 (`references/audit-artifacts/t3-model-companion/2026-09-23/v8-reference-review/sources/hkty-2312.08988v2.pdf`), Theorem 3.3: "Let K be
a model complete field and G a semisimple and split algebraic group over K.
Then the groups G(K)' and G(K) are model complete." Pure group language
(Theorem 3.1, and "model complete" for a structure means its complete theory
is model complete). Matches v8; no journal reference listed on arXiv as of
today.

### Fracek-Kowalski (line 147)

arXiv:2512.09414v2 (`references/audit-artifacts/t3-model-companion/2026-09-23/v8-reference-review/sources/fk-2512.09414v2.pdf`), Theorem 3.6: "Let K be a
field. Then the group H(K) is model complete if and only if K is a model
complete field", H(K) the 3x3 upper unitriangular group. Matches v8.

### Levi-van der Waerden 1933 (lines 167, 609)

Published PDF and page renders in `references/` (pp. 154-158). (5)-(6),
p. 155: (i,k) = i k i^{-1} k^{-1}, (i,j,k) = ((i,j),k); "die zweiten
Kommutatoren liegen im Zentrum" (class <= 3). Normal form (8), p. 156, and
Satz 1, pp. 156-157: order 3^{C(n,1)+C(n,2)+C(n,3)}, unique representation
by (8). v8 Notation (line 231) uses [a,b] = a b a^{-1} b^{-1} and
left-normed iterated commutators, identical to the source. The rank-3 case
has a nonzero triple-commutator coordinate, so class 3 is attained. Fact 2.27
and line 167 match. Remark (line 619, infinite rank) is a correct derived
statement, not a claim of the source.

### Ivanov 1992 (line 183)

arXiv:math/9210221 (author copy of Bull. AMS 27 (1992) 257-260,
`references/audit-artifacts/t3-model-companion/2026-09-23/v8-reference-review/sources/ivanov-1992-arxiv.pdf`), Theorem A: m > 1, n >= 2^48 implies B(m,n)
infinite; Crossref abstract identical. Covers all primes >= 2^48. Rank m > 1
must be stated in v8 (Finding 3).

## Bibliography metadata

Checked against Crossref (DOI records), arXiv abstract pages, RIMS, Springer
and Google Books on 2026-09-23.

| Key | Record | Result |
| --- | --- | --- |
| ChangKeisler1990 | 3rd ed., Elsevier/North-Holland 1990, Studies in Logic 73 | matches |
| dElbeeMuellerRamseySiniora2025 | J. Algebra 662 (2025) 640-701, doi 10.1016/j.jalgebra.2024.08.012 | matches |
| EklofFischer1972 | Ann. Math. Logic 4 (1972) no. 2, 115-171, doi 10.1016/0003-4843(72)90013-7 | matches (spelling "Fischer" per Crossref and the paper) |
| EklofSabbagh1971 | Ann. Math. Logic 2 (1971) no. 3, 251-295, doi 10.1016/0003-4843(71)90016-7 | matches |
| FracekKowalski2025 | arXiv:2512.09414, v1 10 Dec 2025, v2 8 Feb 2026 | matches |
| HoffmannKowalskiTranYe2023 | arXiv:2312.08988, v1 14 Dec 2023, v2 2 Mar 2025 | matches |
| Ivanov1992 | Bull. AMS (N.S.) 27 (1992) no. 2, 257-260, doi 10.1090/S0273-0979-1992-00305-1 | matches (DOI could be added) |
| LeviVanDerWaerden1933 | Abh. Math. Sem. Univ. Hamburg 9 (1933) 154-158, doi 10.1007/BF02940639 | matches |
| Maier1989 | J. Algebra 127 (1989) no. 2, 279-289, doi 10.1016/0021-8693(89)90253-6 | matches |
| Saracino1974 | Trans. AMS 197 (1974) 327-339, doi 10.1090/S0002-9947-1974-0342391-5 | matches |
| Saracino1976 | Israel J. Math. 25 (1976) no. 3-4, 241-248, doi 10.1007/BF02757003 | matches |
| SaracinoWood1979 | J. Algebra 58 (1979) no. 1, 189-207, doi 10.1016/0021-8693(79)90199-6 | matches |
| Takeuchi2022 | RIMS Kokyuroku 2218 (2022) 79-84 | matches |

## Evidence files

Publisher PDFs are registered in `references/` (MANIFEST sections 16-21), with
one-time text extracts in `references/extracted-text/` and 180 DPI renders of
the proof-critical pages in `references/rendered-pages/`.

| Key | File in `references/publications/` | Provenance | SHA-256 |
| --- | --- | --- | --- |
| eklof-sabbagh-1971 | eklof-sabbagh-1971-model-completions-and-modules-published.pdf | user-supplied ScienceDirect PDF `1-s2.0-0003484371900167-main.pdf`, 2026-09-23 | 2889f9fdadc4d9462971ae5a26a86e09fa805abc91c27a6a93cc9e956cbb4b92 |
| eklof-fischer-1972 | eklof-fischer-1972-elementary-theory-of-abelian-groups-published.pdf | user-supplied ScienceDirect PDF `1-s2.0-0003484372900137-main.pdf`, 2026-09-23 | 46396663dd3da750c95cf1e2ade3979dca18c23c8e8ca79a466e22fc121a2f9b |
| saracino-wood-1979 | saracino-wood-1979-periodic-existentially-closed-nilpotent-groups-published.pdf | user-supplied ScienceDirect PDF `1-s2.0-0021869379901996-main.pdf`, 2026-09-23 | 0821a6cb5866bae51df4572e05036ca9f76dc357c9f9a297c9eb8a1e001d0060 |
| maier-1989 | maier-1989-nilpotent-groups-of-exponent-p-published.pdf | user-supplied ScienceDirect PDF `1-s2.0-0021869389902536-main.pdf`, 2026-09-23 | 4a13a6dba2eadf35423b0c2fe89a6ca10abbd31a89ddb59950d89f4dc3eac63d |
| saracino-1974 | saracino-1974-wreath-products-existentially-complete-solvable-groups-published.pdf | Internet Archive capture 20231202212007 of the AMS journal PDF | c21795385728a024229f52a718adb777a7e65b77e0c5130ea23e5ca26e5e3b9e |
| takeuchi-2022 | takeuchi-2022-model-companions-of-some-classes-of-groups-published.pdf | RIMS Kokyuroku PDF `2218-10.pdf` (size 4946263 bytes matches the server) | a41f35c6afa86d9984059ddd566bc923945d28a1ffa2fe7eb6567471cf452b94 |

The Internet Archive copies of the CORE mirrors of Maier 1989, Eklof-Sabbagh
1971 and Eklof-Fischer 1972 that were read before the publisher files arrived
(SHA-256 7ddafe1d..., a11bb4e5..., 4c39cae2...) and the audit copy of the AMS
Saracino 1974 PDF were removed from this directory as superseded.

Evidence saved by the earlier partial notes and kept here:

| File | Source | SHA-256 |
| --- | --- | --- |
| `references/audit-artifacts/t3-model-companion/2026-09-23/v8-reference-review/sources/takeuchi-2022.pdf` | same file as the registered copy above | a41f35c6afa86d9984059ddd566bc923945d28a1ffa2fe7eb6567471cf452b94 |
| `references/audit-artifacts/t3-model-companion/2026-09-23/v8-reference-review/demrs2025.pdf` | arxiv.org/pdf/2310.17595v3 | 54ff26d744f7314a57268279a85114c9d5777b86e30276e5957470387ed32cdb |
| `references/audit-artifacts/t3-model-companion/2026-09-23/v8-reference-review/sources/hkty-2312.08988v2.pdf` | arxiv.org/pdf/2312.08988v2 | 46ac1a8d7aac13bb4d193c6b51386b76f3b6ec30d1efe9d8c06db7f448ed96c4 |
| `references/audit-artifacts/t3-model-companion/2026-09-23/v8-reference-review/sources/fk-2512.09414v2.pdf` | arxiv.org/pdf/2512.09414v2 | 3450f37f578126582da6f4e1a62cdfa0ea2032dea136044503b9d84bb84d540e |
| `references/audit-artifacts/t3-model-companion/2026-09-23/v8-reference-review/sources/ivanov-1992-arxiv.pdf` | arxiv.org/abs/math/9210221 | 873cfd389b1669bf7c4262e2b2effbde6b64e716b7f96727a6734f4e69464e08 |

These arXiv copies are alternatives to closed publisher versions; registering
them in `references/` needs the user's approval under the references policy.

## Not obtained

- Saracino 1976 full text (the publisher abstract states the cited claim
  verbatim).
- Published (journal) version of d'Elbee et al.; Corollary numbering checked
  only in arXiv v3.

> Historical redaction: private source locations and internal revision identifiers have been omitted. Mathematical claims and recorded historical check results are unchanged; this does not report a new verification run.
