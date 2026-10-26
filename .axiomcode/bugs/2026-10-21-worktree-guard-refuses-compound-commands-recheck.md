# Claude Code worktree guard refuses non-git compound commands (substring /git/i test): duplicate of #14740, reproduced again

- Date: 2026-10-21
- Outcome: not ours (AxiomCode issue already filed, #14740; upstream drafted in the earlier record)
- Blame: Claude Code 2.1.286 (bundled claude_agent_sdk `claude`), minified worktree-isolation guard (`aHn=/git/i` tested on the full text of non-simple commands; fail-closed "too complex" on a differential parse). Full analysis is in the main checkout's `.axiomcode/bugs/2026-10-20-worktree-guard-refuses-compound-commands.md`.
- Issue: https://github.com/AxiomMath/axiom/issues/14740 (existing, axiomcode-v5). No new comment, because nothing new beyond one more occurrence.

## What was done
A worker ran a python3 heredoc editing Map.md, followed by `grep -n ... Map.md | wc -l`.

## What came back (verbatim)
"This agent is isolated in the worktree ..., but this command is too complex to verify that it stays inside the worktree. Refusing to run it — a worktree-isolated agent's git operations must target its own worktree." (also "names git in a form too complex to verify")

## Expected
Commands that run no git and touch only worktree paths should run.

## Reproduction
Reproduced in this investigator (worktree-isolated) on 2026-10-21. A `gh issue view ... --jq '.title,...'; for q in ...; do gh issue list ...; done` compound was refused with "runs gh with the text ... inside a construct too complex to verify, so what it runs cannot be shown not to be git". Split into single commands, it ran.

## Cause
See the 2026-10-20 record.

## Versions
Claude Code 2.1.286; AxiomCode 0.5.103.

## Related issues and PRs
AxiomMath/axiom#14740 (open).

## Workaround
Use one plain command per Bash call. Write scripts with the Write tool and then run them. Keep the letters g-i-t out of compound command text.

## Upstream draft
See the 2026-10-20 record (anthropics/claude-code draft, for the user to post or not; not posted).
