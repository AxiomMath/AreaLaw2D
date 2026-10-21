# Claude Code Bash run_in_background task reports exit 143 while its vbp/lean descendants keep running orphaned

- Date: 2026-10-21
- Outcome: not reproduced (not ours: Claude Code)
- Blame: Claude Code Bash tool (background task kill) — not pinned
- Issue: none — Claude Code is outside AxiomMath, the cause is not pinned, and the orphaning did not reproduce with TaskStop

## What was done
Bash tool, run_in_background: `bash .../bp.sh exe vbp build > .../render3.log 2>&1` (bp.sh runs `timeout 3500 lake exe vbp build`).

## What came back (verbatim)
Task reported "failed with exit code 143" twice while the vbp/lean children kept running orphaned (two concurrent `vbp build` processes writing one log, seen with ps).

## Expected
Either the task stays alive or its children are killed.

## Reproduction
Evidence observed 2026-10-21 07:11Z: orphan `vbp build` pid 157428 (ppid 1, pgid 157327, sid 157326, started 07:06:33) with child `lean .../AreaLawBlueprintMain.lean` pid 158163, stdout/stderr -> render4.log, running concurrently with the setsid workaround run (pid 160567 tree), also writing render4.log. The pgid (157327) differs from the sid (157326): GNU `timeout` (no --foreground) moves its child into its own process group. render4.log stopped growing at 07:07:20, ~50 s after start, so the kill was not the 30-min background timeout. The orphan had exited by ~07:14Z.

Tried: (1) a background `bash` with a `sleep 420` child — stayed alive >1.5 min, no 143; (2) a background script running `timeout 600 bash -c 'sleep 601'`, then TaskStop — the whole tree, including timeout's own process group, was killed, no orphan. So the orphaning does not reproduce via TaskStop; what sent SIGTERM to the task in the real run is unknown (not the default 1800 s limit).

## Cause
unknown. Hypothesis: something terminated only the task's bash (exit 143) without the tree-kill TaskStop does, and `timeout`'s separate process group kept lake/vbp/lean alive.

## Versions
Claude Code agent claude-code_2-1-286 (CLAUDE_AGENT_SDK_VERSION=0.2.163); AxiomCode 0.5.103; Debian 12.

## Related issues and PRs
AxiomMath/axiom#12900 (closed): sandbox reboot kills long local runs after 30 min idle — different (kills everything). #14461, #14114 (pre_pr_gate timeout orphaning cachiom) — similar orphaning theme, different component.

## Workaround
`setsid nohup ... ; echo $? > done-marker` and poll the marker; avoid two renders sharing one log / _out dir (check `ps` for a stale `vbp build` first).

## Upstream draft
(Reproduction NOT run end to end.) Target: anthropics/claude-code, new issue, for the user to post or not:
"Bash run_in_background task reports exit 143 but leaves descendants in another process group running. A background `bash script.sh > log` whose script runs `timeout N lake exe vbp build` was reported failed with exit 143 ~50 s after start; `vbp` and its `lean` child continued with ppid 1 in timeout's process group, writing the same log as a later run. TaskStop on an equivalent job kills the whole tree, so the 143 came from another kill path that signals only the task's own process group/session. Expected: the task's descendants are killed with it (or the task is not killed)."
