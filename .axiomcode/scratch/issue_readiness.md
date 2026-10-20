**What happens.** `readiness.ensure` calls a tree "ready" for a local Lean run when only Mathlib and its own dependencies have oleans. A require that no cache supplies (here Physlib, which provides `QuantumInfo.*`) is left out of the check. So `lean_diagnostic_messages` on a file that imports it goes to `lake`, compiles Physlib from source inside the call, and comes back `timed out after 600s — nothing was checked`. The docstring's assumption, that such a package is "Lake's to compile — seconds, not hours", does not hold for Physlib.

**Reproduction.** Project `/root/dev/AreaLaw2D-internal-18b3b627`: lakefile requires mathlib `v4.33.0` and Physlib `a50684a1919e84dc1c761028ff4f77cd59e2de6b`. It has `Comparator/comparator.json` and no charter, so `is_publication` is True and there is no Axile route. `axc prepare` has finished (`prepare.json`: `state: done`, `step: mathlib oleans fetched`). `.lake/packages/Physlib/.lake/build` does not exist.
```
cd /root/dev/AreaLaw2D-internal-18b3b627
axc python -c "
from pathlib import Path; from axiomcode import readiness as R
r=Path('.').resolve()
print('physlib cacheable', 'physlib' in R.cacheable(r)); print('missing', R.missing_packages(r)); print('roots', sorted(R.import_roots(r)))"
```
Then call `lean_diagnostic_messages(path="AreaLawRefactored/S02_Preliminaries.lean", start=1, end=5)`. That file imports `Arealaw.Subadditivity`, and the imports reach `QuantumInfo.*`.

**Actual output.**
```
physlib cacheable False
missing []
roots ['AreaLawForMathlib', 'Arealaw', 'Challenge', 'Mathlib', 'OpenAI', 'QuantumInfo', 'Solution', 'of']
```
```
{"success": false, "items": [], "timed_out": true, "error": "timed out after 600s — nothing was checked",
 "substrate": "local Lean, with the project's options (the Axile environment lacks Physlib (a require left out when it was provisioned, because it did not build), and this file imports it)"}
```
After the call, `.lake/packages/Physlib/.lake/build/lib/lean/{Physlib,QuantumInfo}` exist and are partly built. The in-call `lake` was compiling Physlib when the 600 s ran out.

**Expected.** One of two things. Readiness counts every require the file's imports reach, cacheable or not. Or the local route declines up front with a `not_built`-style answer naming the package and a `next` (for example `lake build QuantumInfo` as a detached job, the way `axc prepare` handles Mathlib). It should not spend 600 s of a gate call compiling a dependency and then report "nothing was checked" with no reason.

**Cause.** [`readiness.py:146`](https://github.com/AxiomMath/axiom/blob/009f2559a9323e57f367721bca9c5ee6e7116818/agents/definitions/axiomcode/v5/src/axiomcode/readiness.py#L146) (`if owner.name.lower() in wanted and not ...olean`) counts a package as missing only if it is in `cacheable()` ([L114-127](https://github.com/AxiomMath/axiom/blob/009f2559a9323e57f367721bca9c5ee6e7116818/agents/definitions/axiomcode/v5/src/axiomcode/readiness.py#L114-L127)), which is Mathlib plus Mathlib's manifest. The docstring at L117-118 justifies this with "seconds, not hours". [`ensure`](https://github.com/AxiomMath/axiom/blob/009f2559a9323e57f367721bca9c5ee6e7116818/agents/definitions/axiomcode/v5/src/axiomcode/readiness.py#L350-L352) then returns `ready` and the local check runs. A possible fix: keep the fetch limited to cacheable packages, but make `missing_packages` report non-cacheable owners with absent oleans as a separate `unbuilt` set. `ensure` would then answer `preparing`/`unavailable` for them and start (or name) a detached `lake build <roots>`.

The timeout reply also keeps the false substrate reason from #12704, so the agent is told that an Axile environment lacks Physlib when the project has no environment at all.

**Versions.** Plugin and substrate 0.5.103 (editable `/opt/axiomcode/src`). Claude Code 2.1.286. `readiness.py` is byte-identical to `main` at 009f2559a9. Lean v4.33.0, Mathlib v4.33.0, Physlib a50684a1.

**Related.** #12704 (wrong "environment lacks Physlib" reason, seen in the same calls). #12706 (lean_run_code's local route skips the readiness gate, the same family for Mathlib). #12645 (the belt cannot use the sandbox's live Axile session, which here built Mathlib+Physlib and answered in about 15 min). #13394 (readiness links only mathlib from siblings). #12968 ("readiness ignores project modules").
