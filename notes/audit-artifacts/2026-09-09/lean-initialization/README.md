# Initial Lean verification

The final `python3 scripts/check.py` run passed all six gates with zero warnings.
`checks.json` records the exact commands, input SHA256 hashes, exit codes, and elapsed seconds.
The run checked a stable input snapshot. Dependency artifacts were cached; this was not a clean
rebuild of mathlib or an observed GitHub Actions run.

- `build.log`: build of the new `T3` library.
- `imports.log`: mathlib `mk_all --check --lib T3`.
- `environment-lint.log`: the standard environment lint of the complete imported project.
- `text-lint.log`: every mathematical source module, including the root, with no exceptions.
- `axioms.log`: every declaration originating in a project module, including unused private
  declarations and declarations in standard namespaces. Only `propext`, `Classical.choice`, and
  `Quot.sound` are allowed.
- `declarations.json`: 130 declarations in four source modules. Of these, 78 have private names;
  52 are exported through `T3`. Public visibility is checked in a separate exported environment.
- `paper-map.log`: source coverage, declaration locators, generated documentation, and actual
  bindings matched against the checked Lean environment inventory.

`check_audit_fixtures.py` and `axiom-fixtures.log` record independent temporary fixtures. The
positive fixture verifies that an unused private theorem and a theorem in the `Nat` namespace are
both audited. The two negative fixtures compile successfully but their audits fail: one introduces
an unused private axiom, the other a public axiom in `Nat`. These runs used the final auditor.
The fixture runner itself exits zero after asserting the expected results.

`check_visibility_fixtures.py` and `visibility-fixtures.log` separately test exported visibility.
In particular, a public declaration in a module imported through a nonpublic edge is detected as
unexported, even though it has no private name.

The reproduction scripts record the actual local repository path. Change their `repo` variable
when reproducing in a different checkout. Their fixtures live outside the mathematical library.
These controls validate the audit mechanisms; they are not proofs of paper statements.

For the mathematical scope, source revision, and remaining part of Fact 2.15, see
[the checkpoint](../../../initial-lean-checkpoint.md).
