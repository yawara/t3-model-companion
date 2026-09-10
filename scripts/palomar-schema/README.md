# Pinned metadata inputs

These files support the offline project-specific check
`python3 scripts/check_palomar_metadata.py`. It checks metadata and configuration
consistency; it does not run Comparator, prove source fidelity, check public
GitHub access, or constitute Palomar review or approval.

## Upstream schema

`v0.4.schema.json` is copied unchanged from
[mathlib-initiative/formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml/blob/99c678e569c7c4c0772db297c5ddd5e4c9b6322e/schema/v0.4.schema.json),
commit `99c678e569c7c4c0772db297c5ddd5e4c9b6322e`.
It is distributed under Apache-2.0; the upstream license is retained in
`LICENSE`. The schema's own `$id` is preserved, but validation loads this local
file and does not fetch the upstream dispatcher.

The root repository's license must match this reviewed standard Apache-2.0
text, allowing CRLF line endings, and the metadata must declare `Apache-2.0`.
This is a check for this project's chosen license, not a general SPDX detector.

## Classification snapshots

`arxiv-codes.json` and `msc2020-codes.json` contain the sorted keys extracted
from the [PalomarSubmission taxonomy files](https://github.com/PalomarRegistry/PalomarSubmission/tree/ef2fa1eadcb246c2346ddba39b52eaa53d4bb763/taxonomies)
at commit `ef2fa1eadcb246c2346ddba39b52eaa53d4bb763`. The source files are
`arxiv-categories.json` and `msc2020-codes.json`; descriptive values are omitted.
Reproduce each derived file by loading the source JSON object and writing
`json.dumps(sorted(data), indent=2) + "\n"` as UTF-8.
The upstream MIT license and copyright notice are retained in `PALOMAR-LICENSE`.

The local check uses that revision's limits of 1-8 arXiv codes and 0-8 MSC2020
codes. It also checks the selected two theorem names, absence of unspecified
Comparator definitions, NanoDa configuration, source hash, and alignment with
the paper map. Changing the selected result or license requires an intentional
update of this project's check. Classification suitability, authorship,
mathematical claims, and review descriptions still require review.

| File | SHA256 |
| --- | --- |
| `v0.4.schema.json` | `25ff6b25ca4511635aff4443cf20480c15e59dddf19591c730950b442ea54fce` |
| `LICENSE` | `c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4` |
| `arxiv-codes.json` | `aca149ce8d56144aebd1d12ff0bfbe67bd412f36b8401a88704635ff20c24911` |
| `msc2020-codes.json` | `711221fc1a61ac16efd153086836dc3e6debd256de0aef5b41616e75ea4b0333` |
| `PALOMAR-LICENSE` | `10321b0cca2b8025d4b5065dd20e22c1f74da2e872c12363e3601974e093bc21` |
