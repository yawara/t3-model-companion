# Publication-history cleanup

On 2026-09-26, this repository's history was selectively edited to remove private
development and literature-storage identifiers. The 23 existing commits were
retained, together with their authorship and dates; rewriting changed their commit
IDs and removed commit signatures that could no longer verify.

The current Lean sources, manuscript TeX and PDFs, dependency pins, public
citations, and authorship information were preserved. Historical Lean changes were
limited to provenance comments. The manuscript's announcement about large primes
was preserved. Obsolete records specific to external development were removed.

Edited historical audit records are marked as such. Their recorded checks and
input hashes describe the original snapshots, not a new verification of the
edited history. An independent comparison of every mapped commit found no
protected-content changes beyond the selected historical comments and no
remaining occurrences of the targeted identifiers in reachable history.

After the cleanup, `python3 scripts/check.py` passed all eight checks with zero
warnings and unchanged inputs. This validates the current tree independently of
the historical records above. It does not establish a successful remote CI run,
Comparator acceptance, or Palomar registration.
