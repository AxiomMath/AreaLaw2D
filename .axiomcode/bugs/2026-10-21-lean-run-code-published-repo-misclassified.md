# lean_run_code falls to local Lean because AreaLaw2D-internal is misclassified as "a published repo" (duplicate of #14768)

- Date: 2026-10-21
- Outcome: duplicate
- Blame: AxiomMath/axiom (AxiomCode). `src/axiomcode/publish.py:3809` (installed 0.5.103) / `:3840` (main 5f09e618c0), `is_publication`: with no charter file, `Comparator/comparator.json` alone counts as a publication mark. The message comes from `src/axiomcode/tools/axile.py:1322-1330` (same line on main).
- Issue: none filed. https://github.com/AxiomMath/axiom/issues/14768 is open and covers this exact cause and message. I did not comment because this report adds nothing new: the original message already names `lean_run_code`, and the consequences are already recorded there.

## What was done
`mcp__plugin_axiomcode_axiomcode__lean_run_code` on a small snippet importing `AreaLawForMathlib.Analysis.Matrix.AuxiliaryBlock`, in session project /root/dev/AreaLaw2D-internal-18b3b627, with no root argument.

## What came back (verbatim)
"substrate": "local Lean, with the project's options (Axile unavailable: /root/dev/AreaLaw2D-internal-18b3b627 is a published repo, which keeps no Axile environment (it is checked with `lake build` and the comparator). Nothing was checked on Axile; `lean_diagnostic_messages`, `axle_check` and `lean_run_code` answer on the local toolchain.)"

## Expected
The Axile route, or an accurate reason for falling back ("no Axile environment recorded; run axile_provision"). This is the internal working repo: origin is AxiomMath/AreaLaw2D-internal, the name has no -publish suffix, and it holds the draft tree, plans, digest/ and paper/.

## Reproduction
Reproduced, 2026-10-21, in the project root:
```
axc python -c "
from pathlib import Path
from axiomcode import publish, charter
r=Path('.').resolve()
print(publish.is_publication(r), charter.has_charter_file(r), (r/'Comparator/comparator.json').is_file())"
# True False True
```

## Cause
`is_publication` returns `(root / COMPARATOR_CONFIG).is_file() or _readme_has_logo_head(root)` when `has_charter_file` is false. `has_charter_file` is false here because there is no dashboard.toml. The function's own docstring admits that working repos carry the comparator pair too. With `is_publication` true, `AxileSession` at tools/axile.py:1322 raises EnvironmentNotReady with the "published repo" text, and HostedFirst answers locally. The same body is still on main 5f09e618c0 (0.5.105, the latest commit under agents/definitions/axiomcode/v5).

## Versions
- AxiomCode plugin 0.5.103; substrate 0.5.103 (editable /opt/axiomcode/src)
- AxiomCode main: 5f09e618c0 (0.5.105), unfixed

## Related issues and PRs
- #14768 (open, axiomcode-v5): the same defect, with one comment adding the publish_plan and challenge_authored consequences. Duplicate.
- #12587 (open): axile_provision calls any repo without dashboard.toml published. Related, but it is a different code path.
- #13357 (open): lean_goal has no local route. Related.
- #12645 (closed): the belt ignores the sandbox's live Axile session. Different.
- #13406 (open): working/published rules in publish_comment_sweep. Different.
- Local records: 2026-10-21-is-publication-charterless-working-repo.md and 2026-10-21-publish-plan-working-repo-not-found.md.
- No PR fixing is_publication was found.

## Workaround
Use the `mcp__axile__*` tools (diagnostics, axle_check) with absolute paths. They reach the live Axile session directly. Alternatively, record an environment in .axiomcode/axile.toml. Either way, do not rely on the belt's "published repo" reason.

## Upstream draft
none
