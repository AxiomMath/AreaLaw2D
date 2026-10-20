# open_workspace copytrees the whole project incl. .lake/packages (7.8 GB, >15 min); diagnostics timed out

- Date: 2026-10-20
- Outcome: filed (copy slowness); diagnostics timeouts duplicate of existing issues
- Blame: AxiomMath/axile — clients/axile_client/workspace_mcp/server.py:1606 (_stage_copy_tree, shutil.copytree with ignore only for reserved root names). Timeouts: AxiomMath/axiom#12725 / #12726 (60 s HTTP MCP cap), already filed.
- Issue: https://github.com/AxiomMath/axile/issues/3329 ; AxiomCode: https://github.com/AxiomMath/axiom/issues/14406

## What was done
Subagent called capabilities-sidecar axile open_workspace on /root/dev/AreaLaw2D-internal-18b3b627, then mcp__axile__diagnostics on S02_Preliminaries.lean.
## What came back (verbatim)
"open_workspace was still copying the 7.8 GB project after about 15 minutes, so I closed it with keep_files=false"; "the first two calls of mcp__axile__diagnostics timed out" (third succeeded). Transcript: axc subagents show af4fe8b02e.
## Expected
Workspace ready in reasonable time or build artefacts not copied; diagnostics not cut off.
## Reproduction
Not re-run (15+ min). Measured: project 7.8G, .lake/packages 7.8G (mathlib 7.2G, Physlib 153M, batteries 172M), .lake/build 46M. Code read confirms no ignore of .lake.
## Cause
_stage_copy_tree copies everything; see issue body. Timeouts: 60 s Claude Code HTTP MCP cap (#12725/#12726).
## Versions
axile_client installed /opt/axile-workspace/.venv/.../workspace_mcp/server.py (Oct 19); axile main 92aebbc; plugin 0.5.103.
## Related issues and PRs
axile#2794 (same copytree line, different failure), axile#1497 (merged), axiom#12725, #12726, #14281.
## Workaround
Do not open_workspace on projects with a large .lake/packages; use mcp__axile__* (already-running session) and retry or keep calls under 60 s.
## Upstream draft
none
