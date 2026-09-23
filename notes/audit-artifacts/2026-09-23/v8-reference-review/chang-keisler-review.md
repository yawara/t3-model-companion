# v8 citation review: Chang and Keisler, Example 3.5.16

Review date: 2026-09-23. Manuscript checked: `T3_modelcompanion_v8.tex`,
line 136; bibliography lines 1561-1566. No manuscript changes.

## Verdict

The citation is accurate. A publicly served Google Books excerpt from the
1990 third edition identifies **Example 3.5.16, page 199**, and states:

> EXAMPLE 3.5.16. The theory of groups has no model companion.

This directly matches the assertion and locator in v8. Verification used the
book's own excerpt, not a secondary author citing the example. The entire
proof/page was not obtained; the claim and its exact locator were verified
from the public searchable excerpt.

## Primary-source access and provenance

- [1990 edition metadata](https://books.google.com/books/about/Model_Theory.html?id=uiHq0EmaFp0C)
  identifies C. C. Chang and H. J. Keisler, *Model Theory*, edition 3,
  Elsevier, 1990, volume 73 of Studies in Logic and the Foundations of
  Mathematics.
- [1990 edition, page 199](https://books.google.com/books?id=uiHq0EmaFp0C&pg=PA199)
  is the corresponding normal page locator.
- The public Google Books in-volume search request
  `https://books.google.com/books?jscmd=SearchWithinVolume2&q=EXAMPLE+3.5.16&vid=uiHq0EmaFp0C`
  returned HTTP 200 with a search result whose `page_id` is `PA199`,
  `page_number` is `199`, and `snippet_text` contains the complete example
  heading and statement quoted above, followed by the beginning of its proof.
- The same query in the [2013 Dover reprint](https://books.google.com/books/about/Model_Theory.html?id=sRi0AAAAQBAJ)
  independently returned the identical heading and assertion at page 199.
- [Keisler's own book list](https://people.math.wisc.edu/~hkeisler/books.html)
  confirms the North-Holland editions of 1973, 1977, and 1990 and the Dover
  reprint of 2012. The third-edition title page and table of contents are also
  available in this [library-provided scan](https://external.dandelon.com/download/attachments/dandelon/ids/DE004BB2EE63AB94BB152C12579D700396E47.pdf).

The web extraction tool failed to fetch the in-volume-search endpoint, but a
normal unauthenticated Python `urllib.request` HTTP request succeeded. No login,
subscription credentials, or access-control circumvention was used. Only the
publicly returned short excerpts were saved; no attempt was made to reconstruct
unavailable pages from many search requests.

Saved raw responses:

- `references/audit-artifacts/t3-model-companion/2026-09-23/v8-reference-review/sources/chang-keisler-google-uiHq0EmaFp0C-EXAMPLE-3.5.16.json` (decisive 1990 edition evidence).
- `references/audit-artifacts/t3-model-companion/2026-09-23/v8-reference-review/sources/chang-keisler-google-uiHq0EmaFp0C-3.5.16.json`.
- `references/audit-artifacts/t3-model-companion/2026-09-23/v8-reference-review/sources/chang-keisler-google-sRi0AAAAQBAJ-EXAMPLE-3.5.16.json` (Dover reprint cross-check).
- `references/audit-artifacts/t3-model-companion/2026-09-23/v8-reference-review/sources/chang-keisler-google-sRi0AAAAQBAJ-3.5.16.json`.

No correction is necessary. An optional more explicit locator is
`\cite[Example~3.5.16, p.~199]{ChangKeisler1990}`.
