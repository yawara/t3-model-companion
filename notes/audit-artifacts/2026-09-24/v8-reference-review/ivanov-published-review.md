# Ivanov 1992: independently checked supplied publication copy

Review date: 2026-09-24. Scope: the new user-supplied PDF, the assertion at
`T3_modelcompanion_v8.tex:183`, and the bibliography at lines 1601-1604.
No manuscript, MANIFEST, consolidated report, or previously saved evidence
was changed. No web retrieval was needed.

## Result

The supplied PDF contains the **published journal edition** of S. V. Ivanov,
*On the Burnside problem on periodic groups*, Bulletin of the American
Mathematical Society (New Series) **27** (1992), no. 2, **257-260**.
The journal issue header explicitly says **October 1992**; the date in the
PDF's descriptive metadata is not the issue date.

**Theorem A(a), printed p. 258 (PDF p. 2), states the infiniteness of B(m,n)
under the conditions m > 1 and n >= 2^48.** The non-strict inequality was
verified visually. No oddness or additional divisibility restriction occurs
in the 1992 theorem's hypotheses. The previous conclusion based on the
author's arXiv version is confirmed, and the publication page locator is now
directly verified.

This supports v8's sufficiently-large-prime assertion. The small precision
issue remains: line 183 should specify rank at least two, since B(1,p) is
finite cyclic. The theorem needed for the local-finiteness argument can be
stated using rank two alone:

```tex
The free Burnside groups $B(2,p)$ are infinite for such primes
\cite[Theorem~A(a), p.~258]{Ivanov1992}, so this shows the conjecture
for all sufficiently large primes.
```

Both the citation's title and its authorship, year, volume, issue, and pages
agree with the supplied journal copy. The distinct model-companion
nonexistence assertion in the preceding manuscript sentence is an announced
result of the manuscript authors, not a theorem in Ivanov's paper.

## Edition identification and comparison with the earlier copy

The new file has the journal's typeset pages, original printed pagination,
AMS copyright line, receipt date, journal running heads, and complete final
references/address block. These identify the article's publication edition,
as opposed to an author manuscript or the later arXiv re-typesetting.
Its PDF metadata says `Producer: PyPDF2`, so this finding does **not** claim
byte-for-byte identity with a file downloaded directly from AMS. Acquisition
provenance is user-supplied; edition provenance is the journal publication.

The older author copy is
`references/audit-artifacts/t3-model-companion/2026-09-23/v8-reference-review/sources/ivanov-1992-arxiv.pdf`,
SHA-256 `873cfd389b1669bf7c4262e2b2effbde6b64e716b7f96727a6734f4e69464e08`.
It numbers pages 1-4 and has its own first-page publication-information
header. Theorem A on its p. 2 has the same hypotheses and infiniteness
conclusion as the new journal copy's p. 258. This review compares those
relevant statements; it does not claim an exhaustive byte/text collation of
every sentence in both editions.

The journal article is four pages of statements and proof remarks. On p. 260
the text explicitly turns to remarks about the proofs of Theorems A-C.
Accordingly, possessing the complete published 1992 article does not mean
possessing a full detailed proof of the underlying Burnside theorem; the
separate 1994 paper remains the full-proof reference discussed in the earlier
audit. The citation-fidelity question at v8:183 is settled by Theorem A(a).

## Files, page mapping, and checksums

The original supplied file was preserved at
`references/on-the-burnside-problem-on-periodic-groups-5fnzsr8mqf.pdf`.
It has 4 PDF pages; PDF page k corresponds to printed page 256+k.

| Artifact | SHA-256 |
| --- | --- |
| Original supplied PDF | `65a841d38331a1376b5c54988a9ab4ceee1e6186b92a39b14db78aa7db737ec2` |
| `references/extracted-text/ivanov-1992-burnside-problem-on-periodic-groups-user-supplied.txt` | `cdff15b997633baefeb5be5b9cd3abaee12480a58126299d6df2f5caa9c8d75a` |
| `references/rendered-pages/ivanov-1992/p0257-title-and-abstract.png` | `8b87de954dcb5906f642bb816837a9dd01b2f5c96c8cbe3d0df6c33f00870c0b` |
| `references/rendered-pages/ivanov-1992/p0258-theorem-a.png` | `3f6fef4166f2ae21d40e794a2b2a0f0240622c0d51de994397f515b07fe54afc` |
| `references/rendered-pages/ivanov-1992/p0260-proof-remarks-and-references.png` | `b6fca161336b44d59a684e047c212f88c732b8c156a9d8c70d071625cecda446` |

The complete retained images of pp. 257, 258, and 260 were inspected. The
embedded OCR is a locating aid only: it turns `>=` into `>` and garbles
superscripts and the symbol B. The rendered p. 258 clearly gives `n >= 2^48`.

Manuscript hash before this review:
`9546045ccd5cb0170ac54fe1485d356765400ed938c57442da558c41c51fa38c`,
unchanged from the preceding review.

## One-time extraction and retained rendering commands

Read `references/README.md` and the helper scripts first; checked that no
existing Ivanov 1992 extract or retained page renders were present. Commands
were run once from `/home/ywr/t3-model-companion` and produced new files only:

```bash
references/scripts/extract-once.sh \
  references/on-the-burnside-problem-on-periodic-groups-5fnzsr8mqf.pdf \
  references/extracted-text/ivanov-1992-burnside-problem-on-periodic-groups-user-supplied.txt

references/scripts/render-page-once.sh \
  references/on-the-burnside-problem-on-periodic-groups-5fnzsr8mqf.pdf 1 180 \
  references/rendered-pages/ivanov-1992/p0257-title-and-abstract.png

references/scripts/render-page-once.sh \
  references/on-the-burnside-problem-on-periodic-groups-5fnzsr8mqf.pdf 2 180 \
  references/rendered-pages/ivanov-1992/p0258-theorem-a.png

references/scripts/render-page-once.sh \
  references/on-the-burnside-problem-on-periodic-groups-5fnzsr8mqf.pdf 4 180 \
  references/rendered-pages/ivanov-1992/p0260-proof-remarks-and-references.png
```

All renders retain the complete page at 180 DPI. Registration and any update
to source-holding counts belong to the parent task, not this independent
review note.
