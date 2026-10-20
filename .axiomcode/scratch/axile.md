**What happens.** `open_workspace` copies the entire source project, `.lake/packages/*` (including every dependency's `.lake/build`) and `.git`, with one `shutil.copytree`. For a Mathlib+Physlib project that is 7.8 GB, and the workspace stayed `opening` for ~15 minutes until the caller closed it.

**Reproduction.** `open_workspace(source_path="/root/dev/AreaLaw2D-internal-18b3b627")` (capabilities-sidecar), then poll `workspace_status`. Project: `du -sh .` = 7.8G, of which `.lake/packages` 7.8G (mathlib 7.2G, Physlib 153M, batteries 172M); `.lake/build` is only 46M. Not timed to completion: the caller gave up at ~15 min (transcript via `axc subagents show af4fe8b02e`).

**Actual.** Still copying after ~15 min; closed with `keep_files=false`.

**Expected.** The managed copy needs sources and manifest, not the package build trees; the session builds its own environment remotely. A copy should skip (or hardlink/reflink) `.lake/packages/*/.lake/build`, `.lake/build`, and `.git`, or at least be bounded and report progress.

**Cause.** [`_stage_copy_tree`](https://github.com/AxiomMath/axile/blob/92aebbc71275a47c2857da294ccd5a16fe50a9e2/clients/axile_client/workspace_mcp/server.py#L1606): `shutil.copytree(record.source, destination, dirs_exist_ok=True, ignore=_ignore)`; `_ignore` (L1573) only drops reserved root names, so everything else is copied. Same line as #2794 (different symptom: that one fails on a vanished tmp file; this one is size/time). A shared fix, an ignore list for build outputs, would address both.

**Versions.** Installed `axile_client` at /opt/axile-workspace/.venv/lib/python3.14/site-packages/axile_client/workspace_mcp/server.py (Oct 19); line read on main 92aebbc71275a47c2857da294ccd5a16fe50a9e2. AxiomCode plugin 0.5.103.

**Related.** #2794 (same copytree, different failure); #1497 (merged, managed workspace storage). The accompanying diagnostics timeouts are AxiomMath/axiom#12725/#12726, not this bug.
