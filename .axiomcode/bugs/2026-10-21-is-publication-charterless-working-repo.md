# is_publication calls a charter-less working repo published whenever Comparator/comparator.json exists: AreaLaw2D-internal declined Axile as 'a published repo' (publish.py:3840)

- Date: 2026-10-21
- Outcome: filed (classification). The substrate-choice part is fixed upstream (in 0.5.104 and later, `lean_diagnostic_messages` is drake first, #14408) but not yet installed (0.5.103). The local 600 s timeout duplicates #12968 / #14281.
- Blame: AxiomMath/axiom (AxiomCode). `src/axiomcode/publish.py:3809` installed, `:3840` on main 5f09e618c0. Consequence in 0.5.103: `tools/backend.py:377` skips auto-provision, and `tools/axile.py:1322` gives the "published repo" message.
- Issue: https://github.com/AxiomMath/axiom/issues/14768

## What was done
`mcp__plugin_axiomcode_axiomcode__lean_diagnostic_messages(path="AreaLawRefactored/S08_Comparators/Setup.lean", root=<this worktree>, start=1, end=80)`

## What came back (verbatim)
{"success": false, "items": [], "timed_out": true, "error": "timed out after 600s — nothing was checked", "substrate": "local Lean, with the project's options (Axile unavailable: /root/dev/AreaLaw2D-internal-18b3b627/.claude/worktrees/agent-a42c42c925e676ea4 is a published repo, which keeps no Axile environment (it is checked with `lake build` and the comparator). Nothing was checked on Axile; `lean_diagnostic_messages`, `axle_check` and `lean_run_code` answer on the local toolchain.)"}

## Expected
AxiomMath/AreaLaw2D-internal is a working repo, not a `-publish` sibling, so it should not be classified as published. It should be checked on Axile; the plain `mcp__axile__diagnostics` works on the same paths.

## Reproduction
Reproduced:
```
axc python -c "
from pathlib import Path
from axiomcode import publish, charter
r=Path('.').resolve()
print(publish.is_publication(r), charter.has_charter_file(r), (r/'Comparator/comparator.json').is_file(), publish._readme_has_logo_head(r))"
# True False True False
```

## Cause
- `is_publication`: when there is no charter, `Comparator/comparator.json` alone makes a repo published. The function's own docstring says working repos carry the pair too. This repo has no dashboard.toml, no `.axiomcode/axile.toml`, and no logo README.
- In 0.5.103, `backend.py:377` therefore refuses to auto-provision, so the call goes local.
- The local route then timed out because the worktree's `.lake/build` holds oleans only for part of S06/S07 (`AreaLawRefactored.S01`..`S05` and `S08` are unbuilt), and readiness ignores unbuilt project modules (#12968). The Physlib part is #14281.

## Versions
- AxiomCode plugin 0.5.103; substrate 0.5.103 (editable /opt/axiomcode/src)
- axile_client 0.1.0 (wheel /opt/axiomcode/wheels)
- AxiomCode main 5f09e618c0 (0.5.105), where `is_publication` is unchanged

## Related issues and PRs
- #14281 (open): readiness and Physlib, same project. It records is_publication=True as a fact, not as a defect.
- #12704 (open): the false "lacks Physlib" reason.
- #12587 (open): the inverse case, `axile_provision` calling a non-publication repo published.
- #12645 (closed by PR #14545): the belt ignores the sandbox's live Axile session.
- #12968 (open): readiness ignores unbuilt project modules.
- AxiomCodeV5#289 (closed): the inverse misclassification.
- PR #14408: drake replaces Axile.
None of these is a duplicate of the classification defect.

## Workaround
Use `mcp__axile__diagnostics` / `mcp__axile__axle_check` with absolute paths. Do not retry a call that timed out; see #14633. Or build the upstream modules first with a detached `lake build AreaLawRefactored.S07_Transport`, so the local route has oleans.

## Upstream draft
none
