# Session push of .github/workflows/blueprint.yml rejected: bridge token lacks `workflows` (duplicate of AxiomMath/axiom#14210)

- Date: 2026-10-21
- Outcome: commented
- Blame: AxiomMath/axiom agents backend — agents/backend/app/projects/git_routes.py:49 (`WRITE_PERMISSIONS = {"contents": "write"}`, used at :193), still so on main today; AxiomCode's part: mathlib-quality/references/blueprint-conventions.md:33-35, :493-498 tell agents to ship .github/workflows/ files with no session-clone caveat
- Issue: commented https://github.com/AxiomMath/axiom/issues/14210#issuecomment-6310262665

## What was done
`git push origin HEAD:agents/18b3b627-b93d-5732-9c67-7919d1fb0eea-blueprint` of a commit adding `.github/workflows/blueprint.yml` (Step 3 of RefactoringPlan.md requires blueprint CI).

## What came back (verbatim)
```
To https://staging.agents.axiommath.ai/api/git/sessions/18b3b627-b93d-5732-9c67-7919d1fb0eea
 ! [remote rejected] HEAD -> agents/18b3b627-b93d-5732-9c67-7919d1fb0eea-blueprint (refusing to allow a GitHub App to create or update workflow `.github/workflows/blueprint.yml` without `workflows` permission)
```

## Expected
Push succeeds, or the agent is warned before committing that workflow files cannot be pushed from a session.

## Reproduction
Per #14210: in any platform session clone, commit a change under .github/workflows/ and push the session branch. Not re-run here (the reported output is the reproduction; #14210 has the same message).

## Cause
Bridge mints a contents-only installation token (git_routes.py:49, :193 on main, confirmed via gh api today). Fix PR AxiomMath/axiom#12492 "agents: forward bridged pushes with the agents' token" OPEN, last update 2026-10-10.

## Versions
AxiomCode plugin/substrate 0.5.103; v5 dir head 5f09e618.

## Related issues and PRs
- AxiomMath/axiom#14210 (open, axiomcode-v5): same bug, general case -> duplicate; commented with the new path (blueprint workflow prescribes workflow files) and current status.
- AxiomMath/axiom#12983 (open): launchproject scaffold variant.
- AxiomMath/AxiomCodeV5#275 (open, legacy): launchproject variant.
- AxiomMath/axiom#12492 (open PR): upstream fix.

## Workaround
File committed at blueprint/ci/blueprint.yml for the user to move into .github/workflows/.

## Upstream draft
none (upstream is AxiomMath; covered by #14210 / #12492)
