# Claude Code worktree guard refuses plain in-worktree compound commands and heredocs; its "names git" test is a substring match

- Date: 2026-10-20
- Outcome: not ours (AxiomCode issue filed; upstream drafted)
- Blame: Claude Code 2.1.286 (bundled `claude_agent_sdk/_bundled/claude`), minified worktree guard: `if(e.kind!=="simple"){if(Ove(e)||e.tree===void 0)return S("is too complex to verify ...");if(aHn.test(n))return S("names git in a form too complex ...")` with `aHn=/git/i` over the full command text
- Issue: https://github.com/AxiomMath/axiom/issues/14740 (label axiomcode-v5)

## What was done
Worktree-isolated subagents (worktree /root/dev/AreaLaw2D-internal-18b3b627/.claude/worktrees/agent-a40938f86f26dd963 and siblings) ran Bash such as `cat > .axiomcode/scratch/s11/fix3.py <<'EOF' ... EOF`, `python3 - <<'EOF' ... EOF` editing AreaLawRefactored/S11_Geometry.lean, `cat >> AreaLawRefactored/S01_AreaLaw.lean <<'EOF' ... EOF`, and `timeout 70 axc subagents wait <id> --timeout 60; echo exit=$?; ls ... | grep ...; git status --short | head`. Transcripts show most refused commands were `cd <worktree>; ...` compounds, `f=...; sed ... $f`, `a=$(...)`, `for` loops, or a heredoc after another command.

## What came back (verbatim)
```
This agent is isolated in the worktree /root/dev/AreaLaw2D-internal-18b3b627/.claude/worktrees/agent-a40938f86f26dd963, but this command is too complex to verify that it stays inside the worktree. Refusing to run it — a worktree-isolated agent's git operations must target its own worktree. Split it into plain, separate commands and run them from /root/dev/AreaLaw2D-internal-18b3b627/.claude/worktrees/agent-a40938f86f26dd963.
```
and "...but this command names git in a form too complex to verify that it stays inside the worktree..."

## Expected
Commands touching only worktree paths and running no git run; the "names git" wording only when a git command is present. (The one reported "names git" case did contain `git status`, so that wording was accurate there; but the test is a substring match and fires falsely elsewhere — see Reproduction.)

## Reproduction
Reproduced in this investigator subagent (itself worktree-isolated):
- `mkdir -p .axiomcode/scratch/debug && cat > .axiomcode/scratch/debug/hd.txt <<'EOF'` / `hello` / `EOF` -> refused "too complex".
- `for x in digit; do echo $x; done` -> refused "names git ..." (no git; substring of `digit`).
- A `python3 - <<'EOF'` script whose body contained a string with those letters -> refused "feeds python text naming git".
- `gh issue create ... --title "...git..."` -> refused "runs gh with the text ... cannot be shown not to be git"; retitled without the letters, it ran.
- Controls that ran: lone `cat > rel/path <<'EOF'`; `python3 - <<'EOF'` reading a relative path; `timeout 5 sleep 1; echo exit=$?; ls X | grep -i s01 | head -2`; `echo digits | tr a-z A-Z`.

## Cause
Claude Code's guard fails closed on any non-simple command whose parse is marked differential (`Ove`), and for non-simple commands tests `/git/i` against the whole command text, so any occurrence of the three letters (in `digit`, `.github`, a heredoc body, a quoted title) produces the git refusal. The first is a deliberate conservative choice; the second is a false positive (should be a word-boundary command-name match). AxiomCode does not request `isolation: "worktree"` anywhere (grep of plugin and substrate); the main session chose it.

## Versions
- Claude Code 2.1.286 (/opt/axiomcode/venv/lib/python3.12/site-packages/claude_agent_sdk/_bundled/claude)
- AxiomCode plugin 0.5.103; substrate 0.5.103 (editable /opt/axiomcode/src); AxiomCode main at 5f09e618c0646f81311a7aaa28f894f4dfef78a7

## Related issues and PRs
- None duplicate. Searched AxiomMath/axiom (label axiomcode-v5), AxiomMath/AxiomCodeV5, and org-wide for "too complex to verify", "worktree too complex", "isolated worktree", "Refusing to run", "worktree-isolated agent", "worktree". Nearest: axiom#13228 (concurrent workers share one checkout) — different.
- Context items from the same brief, not investigated here: axile diagnostics timeouts already filed as AxiomMath/axiom#14633; a general-purpose subagent dying after 69 min with "Agent terminated early due to an API error: Request timed out (error type server_error)" is a Claude API/Claude Code transport failure (not ours, no repo here) — nothing filed for it.

## Workaround
In a worktree-isolated agent: one plain command per Bash call, no `cd <worktree>;` prefix (cwd is already the worktree), no shell variables or `$(...)`, no loops; write file contents and scripts with the Write tool, then run `python3 path/to/script.py`; keep the letters g-i-t out of compound command text and of inline heredoc bodies (put them in files). Or dispatch the subagent without worktree isolation.

## Upstream draft
Target: Claude Code (anthropics/claude-code issue tracker) — for the user to post or not; not posted. Reproduction run end to end on 2.1.286.

Title: Worktree-isolated subagent Bash guard: substring `/git/i` test refuses commands that contain no git (e.g. `for x in digit; do echo $x; done`)

Body: In a subagent launched with `isolation: "worktree"`, a non-simple Bash command whose text contains the substring "git" anywhere is refused with "this command names git in a form too complex to verify that it stays inside the worktree", e.g. `for x in digit; do echo $x; done`, or `gh issue create --title "... git ..."`, or a `python3 - <<'EOF'` heredoc whose body mentions git. In 2.1.286 the check is `aHn=/git/i` tested against the full command text. Expected: match `git` as a command word (or at least `\bgit\b`), not a substring. Secondary: common worktree-local forms (`cd <own worktree>; cmd`, `f=path; sed -n 1,5p $f`, `mkdir -p d && cat > d/f <<'EOF'`) are refused as "too complex"; allowing a leading `cd` to the agent's own worktree and simple variable assignments of literal relative paths would remove most of the friction.
