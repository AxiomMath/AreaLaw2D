# Physlib-importing files of a publication-marked repo cannot be checked by any AxiomCode gate; mcp__axile__* times out with no "still building"

- Date: 2026-10-19
- Outcome: filed (new AxiomCode issue #14281) + commented (#12704); the mcp__axile__* timeout is a duplicate of #12725 / #12726 (nothing new to add)
- Blame: three defects.
  (a) AxiomMath/axiom (AxiomCode), `src/axiomcode/readiness.py:146` and `:114-127`. Readiness ignores non-cacheable requires, so the local route compiles Physlib in-call.
  (b) AxiomMath/axiom (AxiomCode), `src/axiomcode/tools/axile.py:2163-2176` (`absent_packages`) and `:1801` (`cannot_serve`). With no environment recorded, the substrate claims "the Axile environment lacks Physlib".
  (c) AxiomMath/axiom `agents/definitions/base/sidecar/axile-session/server.py:462-463` (json_response, #12725) together with AxiomCode `acp_server.py` setting no per-server timeout (#12726). Claude Code cuts mcp__axile__ calls at about 60 s.
- Issue: https://github.com/AxiomMath/axiom/issues/14281 (filed); https://github.com/AxiomMath/axiom/issues/12704#issuecomment-6279419075 (comment). #12725 and #12726 are open duplicates for (c), so nothing was filed for (c).

## What was done
1. `lean_run_code` with `import Arealaw.Subadditivity ...`.
2. `lean_diagnostic_messages` on `AreaLawRefactored/S02_Preliminaries.lean`, which imports OpenAI.Statements and Arealaw.Subadditivity and through them Physlib's QuantumInfo.
3. `mcp__axile__diagnostics` (twice) and `mcp__axile__axle_check` on `Arealaw/Subadditivity.lean`, then `mcp__axile__diagnostics` on S02_Preliminaries.lean.

## What came back (verbatim)
(1a) {"okay": false, "messages": ["timed out; nothing was checked"], "substrate": "local Lean, with the project's options (Axile unavailable: /root/dev/AreaLaw2D-internal-18b3b627 is a published repo, which keeps no Axile environment (it is checked with `lake build` and the comparator). Nothing was checked on Axile; `lean_diagnostic_messages`, `axle_check` and `lean_run_code` answer on the local toolchain.)", ...}
(1b) {"success": false, "items": [], "declined": "this tree is being prepared for a local Lean run (its dependencies are not built: mathlib) ... Next: `axc prepare --root /root/dev/AreaLaw2D-internal-18b3b627 --wait`.", "substrate": "local Lean, with the project's options (the Axile environment lacks Physlib (a require left out when it was provisioned, because it did not build), and this file imports it)"}
(2) four times: `The operation timed out.`

Re-run by the investigator after prepare finished:
{"success": false, "items": [], "timed_out": true, "error": "timed out after 600s — nothing was checked", "substrate": "local Lean, with the project's options (the Axile environment lacks Physlib (a require left out when it was provisioned, because it did not build), and this file imports it)"}

/tmp/axile-mcp.log, where the sidecar finished every call the client had already dropped:
```
AXILE_PROFILE {"path":"Arealaw/Subadditivity.lean","outcome":"ok","queue_ms":0,"open_ms":231555,"operation_ms":77634}
AXILE_PROFILE {"path":"Arealaw/Subadditivity.lean","outcome":"ok","queue_ms":238507,"open_ms":0,"operation_ms":111}
AXILE_PROFILE {"path":"Arealaw/Subadditivity.lean","outcome":"ok","queue_ms":131537,"open_ms":0,"operation_ms":280}
AXILE_PROFILE {"path":"AreaLawRefactored/S02_Preliminaries.lean","outcome":"ok","queue_ms":0,"open_ms":230830,"operation_ms":79035}
```
The fourth call had a new environment id, because the lakefile lean_lib edit changed the identity.

## Expected
The AxiomCode gates check a Physlib-importing file on Axile, or else decline quickly with the real reason and a next step. mcp__axile__* answers, or says "still building", within the client's timeout.

## Reproduction
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
Then `lean_diagnostic_messages(path="AreaLawRefactored/S02_Preliminaries.lean", start=1, end=5)` gives `timed out after 600s`. Reproduced 2026-10-19.

## Cause
- Why there is no Axile route: `Comparator/comparator.json` with no charter makes `publish.is_publication` True (publish.py, `is_publication`). `LeanSession._ensure_environment` (tools/axile.py:1320-1330) and `axile_provision` (tools/axile.py:2419-2427) then refuse Axile by design (#273). The belt cannot adopt the sandbox's live axile-session either (#12645).
- (b) `built_without` returns None when nothing is recorded. `absent_packages` reads None as "an old environment built without every require but Mathlib". `cannot_serve` never checks `self.environment`. So it reports a false "lacks Physlib" (#12704).
- (a) `readiness.missing_packages` (readiness.py:146) counts only `cacheable()` packages, which are Mathlib plus Mathlib's manifest. Physlib's missing oleans are therefore invisible, `ensure` returns ready, and the local lake run compiles Physlib inside the 600 s call. The docstring at readiness.py:117-118 assumes this takes "seconds, not hours" (#14281).
- (c) The sidecar sends no bytes until the result, and acp_server sets no per-server timeout. Claude Code's roughly 60 s HTTP request cap aborts the call. The sidecar's own BUILD_WAIT_SECONDS=600 "still building" message can therefore never arrive. Calls queued behind the per-session lock die as well (#12725, #12726).

## Versions
- AxiomCode plugin and substrate 0.5.103, editable at /opt/axiomcode/src. `readiness.py` and `tools/axile.py` (absent_packages) are identical to AxiomMath/axiom main 009f2559a9323e57f367721bca9c5ee6e7116818.
- axile_client 0.1.0, from the wheel /opt/axiomcode/wheels/axile_client-0.1.0-py3-none-any.whl.
- The sidecar /usr/local/lib/axile-session/server.py is byte-identical to AxiomMath/axiom main (last change d1e936f7366c, 2026-10-15).
- Claude Code 2.1.286 (bundled). Lean v4.33.0, Mathlib v4.33.0, Physlib a50684a1919e84dc1c761028ff4f77cd59e2de6b.

## Related issues and PRs
- #12704 (open): the false "environment lacks Physlib" reason. Commented with the publication-repo variant and 0.5.103.
- #12725 (open, sidecar server.py) and #12726 (open, acp_server timeout): exact duplicates for the mcp__axile__ timeouts. #12725 already records opens over 4 min and lock queueing, so no comment was added.
- #12645 (open): the belt ignores the sandbox's live Axile session for repos with no dashboard.toml.
- #12706 (open): lean_run_code's local route skips the readiness gate.
- #13394, #12968 (open): other readiness gaps.
- AxiomCodeV5 #273, #289, #272 (closed): the background to the publication policy.

## Workaround
Open a workspace with `mcp__capabilities-sidecar__axile__open_workspace` on the project root. It builds Mathlib + Physlib, and then `diagnostics` / `check_module` / `check` answer correctly (about 15 min for the first build). Retrying `mcp__axile__*` after a timeout also works: the sidecar keeps opening the session in the background, and the profile log shows the later calls finishing in under 1 s once it is open. The Physlib local build is now partly done in .lake/packages/Physlib, so `lake build QuantumInfo` (detached) would finish it for the local route.

## Upstream draft
none: every defect is in AxiomMath/axiom.
