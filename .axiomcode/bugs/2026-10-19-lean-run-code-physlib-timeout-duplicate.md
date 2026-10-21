# lean_run_code on a Physlib-importing module times out on the local route (duplicate of #14281 / #12704 / #12706)

- Date: 2026-10-19
- Outcome: duplicate
- Blame: AxiomMath/axiom (AxiomCode). There are two defects.
  (1) src/axiomcode/readiness.py:146 (missing_packages counts only cacheable() packages, so Physlib's missing oleans go unseen).
  (2) src/axiomcode/tools/axile.py:2163-2176 (absent_packages) and :1801 (cannot_serve), which give the false reason "environment lacks Physlib" when no environment is recorded.
  Also relevant: local_lean.py:458, where lean_run_code's local route skips the readiness gate (#12706).
  The cause: the repo is publication-marked (Comparator/comparator.json), so AxiomCode deliberately keeps no Axile environment and every gate goes local.
- Issue: none filed. The bug is already reported and open as https://github.com/AxiomMath/axiom/issues/14281, #12704 and #12706. Full analysis is in 2026-10-19-physlib-gates-no-route-and-axile-timeout.md. This occurrence adds nothing new, so no comment was posted.

## What was done
mcp__plugin_axiomcode_axiomcode__lean_run_code with code `import AreaLawRefactored.S02_Preliminaries\n#check AreaLaw.lemma_2_1`. The project root was the default.

## What came back (verbatim)
{"okay": false, "messages": ["timed out; nothing was checked"], "substrate": "local Lean, with the project's options (the Axile environment lacks Physlib (a require left out when it was provisioned, because it did not build), and this file imports it)", "project_root": "/root/dev/AreaLaw2D-internal-18b3b627"}

## Expected
The snippet elaborates. It does so in seconds in the hosted Axile workspace through mcp__capabilities-sidecar__axile__check_module or diagnostics, which build Physlib. Failing that, the tool should decline quickly and give the true reason.

## Reproduction
Re-run on 2026-10-19; the state is unchanged from the earlier record:
```
cd /root/dev/AreaLaw2D-internal-18b3b627
axc python -c "
from pathlib import Path; from axiomcode import readiness as R, publish as P; from axiomcode.tools import axile as A
r=Path('.').resolve()
print(P.is_publication(r), A.built_without(r), A.absent_packages(r))
print('physlib' in R.cacheable(r), R.missing_packages(r))
print(A.LeanSession('', r, backend=object()).cannot_serve(path='AreaLawRefactored/S02_Preliminaries.lean'))"
# True None {'Physlib': ['Physlib', 'PhyslibAlpha', 'QuantumInfo']}
# False []
# the Axile environment lacks Physlib (a require left out when it was provisioned, because it did not build), and this file imports it
```

## Cause
See 2026-10-19-physlib-gates-no-route-and-axile-timeout.md. In short:
- is_publication is True, so no Axile environment is used. This is by design (AxiomCodeV5 #273).
- built_without is None, so absent_packages wrongly reports Physlib (#12704).
- readiness ignores the non-cacheable Physlib, so the local lake run compiles Physlib's unbuilt modules inside the call and times out (#14281, #12706).

## Versions
- AxiomCode 0.5.103, editable at /opt/axiomcode/src.
- AxiomMath/axiom main for agents/definitions/axiomcode/v5 is still at 009f2559a932 (2026-10-19). Nothing has been fixed since the earlier record.
- Lean and Mathlib v4.33.0; Physlib a50684a1.

## Related issues and PRs
- #14281 (open, 0 comments) is the readiness defect: an exact match.
- #12704 (open) is the false "lacks Physlib" reason: an exact match.
- #12706 (open) is lean_run_code skipping readiness: the same route.
- #12725 and #12726 (open) are the mcp__axile__ client timeouts.
- #12645 (open): the belt cannot adopt the sandbox's live axile session.
- None of these needed a comment, because this occurrence brings no new version, reproduction or line.

## Workaround
Use mcp__capabilities-sidecar__axile__* (open_workspace, then check_module, diagnostics or check) on the project root. That route builds Mathlib and Physlib and answers correctly. To check one #check, write it into a scratch module and use check_source or diagnostics there. Another option is to finish the local Physlib build in the background (`lake build QuantumInfo Physlib`), after which the local route should answer.

## Upstream draft
none: every defect is in AxiomMath/axiom.
