# Children of a worktree-isolated subagent inherit its pin (cannot use sibling worktrees from `git worktree add`; EnterWorktree(path) claims write access it does not grant); plus axiom_audit local build and axile timeouts (duplicates)

- Date: 2026-10-21
- Outcome: (1) not ours (AxiomCode issue filed; upstream drafted); (2) duplicate, commented; (3) duplicate
- Blame:
  - (1) Claude Code 2.1.286 worktree guard (bundled `claude_agent_sdk/_bundled/claude`); AxiomCode's part `plugins/axiomcode/skills/axc/workflows/parallel.md:33-34`
  - (2) AxiomMath/axiom (AxiomCode) `src/axiomcode/tools/lean.py:517-531` (`_cold_audit`) via `readiness.ensure` (`src/axiomcode/readiness.py:342-379`, packages only); trigger: no Axile environment recorded (`tools/backend.py:395-413` returns None), itself #14768
  - (3) AxiomMath/axiom `agents/definitions/base/sidecar/axile-session/server.py` (#12725 headers/60 s cap; #14633 lane lock)
- Issue: (1) https://github.com/AxiomMath/axiom/issues/14819 ; (2) commented https://github.com/AxiomMath/axiom/issues/12968#issuecomment-6306865529 ; (3) none (dup of #12725 / #14633, already commented from this session per 2026-10-21-axile-lane-lock-held-by-cold-build.md)

## What was done
(1) Subagent `agent-a2bf73aa52fc5c1d5` (isolation worktree) created `.claude/worktrees/s09-templates`, `s09-collar`, `s09-data`, `s09-scan` with `git worktree add` and launched four `general-purpose` helpers (no `isolation`), each told to work only in its worktree. Helper `agent-a140c23f02cd489c9` tried Write, `git -C …/s09-templates status`, then `EnterWorktree(path=…/s09-templates)` and Write/Bash again.
(2) `axiom_audit(import_module=AreaLawRefactored.S09_Scanner.Histories, decl=AreaLaw.Scanner.lemma_9_1, root=<this worktree>)`.
(3) `mcp__axile__diagnostics` on a file of a fresh worktree.

## What came back (verbatim)
(1) Write: `This agent is isolated in the worktree /root/dev/AreaLaw2D-internal-18b3b627/.claude/worktrees/agent-a2bf73aa52fc5c1d5. Edit the worktree copy of this file instead of the shared-checkout path.`
EnterWorktree: `Entered worktree at /root/dev/AreaLaw2D-internal-18b3b627/.claude/worktrees/s09-templates on branch agents/18b3b627-s09-templates. This agent's working directory and write access now point at the worktree; the previous directory was left untouched.`
Bash after it (6x): `This agent is isolated in the worktree /root/dev/AreaLaw2D-internal-18b3b627/.claude/worktrees/agent-a2bf73aa52fc5c1d5, but this command's working directory resolved to the shared checkout (/root/dev/AreaLaw2D-internal-18b3b627/.claude/worktrees/s09-templates). Refusing to run it there — a worktree-isolated agent's commands must run inside its worktree. Re-run the command from /root/dev/AreaLaw2D-internal-18b3b627/.claude/worktrees/agent-a2bf73aa52fc5c1d5.`
(2) `"status": "tool_error"`, `lake was still building the imports (8738 of 8774 jobs) when the timeout hit — nothing was checked`.
(3) `The operation timed out.` repeatedly for 30+ minutes.

## Expected
(1) Children can work in a same-repo worktree under `.claude/worktrees/`, or the harness says up front they inherit the pin, and EnterWorktree refuses instead of reporting success. (2) Hosted session, or `not_built` with a next step, not a local build of the project's closure. (3) Bounded first open, or progress.

## Reproduction
(1) Reproduced from transcripts of session 812353ee (`subagents/agent-a140c23f02cd489c9.jsonl`, parent `agent-a2bf73aa52fc5c1d5.jsonl`, whose Agent calls carry no `isolation`). Not re-run live (the s09-* worktrees have since been removed; `git worktree list` shows only the main checkout and this one). Also: the same guard refused my own `gh issue view` with a `-q` jq string and a `gh issue list --search "git worktree add"` (#14740's substring defect).
(2) Code-path reproduction: neither this worktree nor `/root/dev/AreaLaw2D-internal-18b3b627` has `.axiomcode/axile.toml` or `dashboard.toml`, so `backend.axile_session` returns None; `readiness.ensure` checks only `missing_packages` (present, so "ready"); `_cold_audit` returns None; `_run_probe` runs `lake lean` on a scratch importing the module, which builds the unbuilt project modules (36 of 8774 jobs left) until the deadline. Worktree `.lake/build/lib/lean/AreaLawRefactored/` holds only S01_AreaLaw.olean. `nproc` = 4. Not re-run (no Lean, per brief).
(3) Not re-run; matches #12725 / #14633.

## Cause
(1) Claude Code: pin inherited by non-isolated children; `EnterWorktree(path)` does not move the Write/Bash guard's pin; the guard labels any path outside the pin "the shared checkout". AxiomCode: parallel.md:33-34 ("a subagent uses `git worktree add` on a branch of its own") has no caveat for an isolated coordinator.
(2) Readiness ignores the project's own unbuilt modules (#12968); no environment recorded/provisioned because the repo is classified as published (#14768), and `axile_session` never provisions by design. The timeout text's advice "audit from their own modules rather than an umbrella" was wrong here (it already was the declaration's own module).
(3) axile-session sidecar sends no early headers (60 s cap, #12725) and holds the per-(root,lane) lock for a whole cold build (#14633).

## Versions
- AxiomCode plugin 0.5.103, substrate 0.5.103 (editable /opt/axiomcode/src, direct_url file:///opt/axiomcode/src)
- AxiomCode main 5f09e618c0646f81311a7aaa28f894f4dfef78a7: parallel.md:34 and `_cold_audit` (lean.py:558) unchanged
- Claude Code 2.1.286 (bundled)
- Project AxiomMath/AreaLaw2D-internal, branch agents/18b3b627-b93d-5732-9c67-7919d1fb0eea-s09

## Related issues and PRs
- #14819 (filed now): (1).
- #14740 (open): same guard, compound-command / substring defect; not a duplicate of (1).
- #13228, #12891 (open): workers sharing one checkout; the problem parallel.md's rule prevents.
- #12968 (open): (2) duplicate; commented with the no-environment trigger.
- #14768 (open): why no Axile environment exists for this repo.
- #12725 (open), #14633 (open), #14524 (open, drake cold build): (3).

## Workaround
(1) Do not have an isolated coordinator spawn helpers into new worktrees: keep helpers in the coordinator's own worktree on disjoint files (the later "scanner"/"smallbox" helpers did this), or ask the main thread to launch each piece as its own `Agent(isolation: "worktree")`. MCP writes (`lean_apply_edit(root=…)`) are not guarded, but bypassing the guard that way is not recommended. (2) Provision an Axile environment once #14768 is resolved, or build the module's closure first; audit only after its oleans exist. (3) Avoid parallel cold-opens of one root; wait for the first to finish.

## Upstream draft
Target: anthropics/claude-code (new issue; not posted — for the user to decide). Reproduction from transcripts, not re-run end to end.

Title: Worktree-isolated subagent's pin is inherited by its non-isolated children, and EnterWorktree(path) reports write access the Write/Bash guard does not grant

Body: In Claude Code 2.1.286, an agent launched with `isolation: "worktree"` registers a second worktree of the same repo under `.claude/worktrees/` (`git worktree add`), then launches a child with the Agent tool (no `isolation`) told to work there. The child's Write is refused ("This agent is isolated in the worktree <parent's>… Edit the worktree copy of this file instead of the shared-checkout path"). The child calls `EnterWorktree(path=<new worktree>)`, which returns "This agent's working directory and write access now point at the worktree", yet every subsequent Bash is refused with "this command's working directory resolved to the shared checkout (<new worktree>)", and Write still refused. Expected: either EnterWorktree updates the guard's pin (its description says pinned agents may switch to worktrees under `.claude/worktrees/` of the same repo), or it refuses up front; and children's inheritance of the pin is documented. The message should also not call another worktree "the shared checkout".
