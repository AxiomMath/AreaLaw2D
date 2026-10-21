# Pending workflow changes

The agent's push token may not create or update files under `.github/workflows/`
("refusing to allow a GitHub App to create or update workflow … without `workflows`
permission"), so the CI changes of Step 2 are staged here. Someone with that permission
applies them from the repository root:

```bash
cp ci/workflows/lean_action_ci.yaml .github/workflows/lean_action_ci.yaml
git mv ci/workflows/blueprint.yml .github/workflows/blueprint.yml
git rm ci/workflows/lean_action_ci.yaml ci/PENDING_WORKFLOWS.md
git add .github/workflows/lean_action_ci.yaml
git commit -m "CI: scripts/audit.lean, blueprint job"
git push
```

What changes:

| File | Change |
|---|---|
| `.github/workflows/lean_action_ci.yaml` | the mk_all check stays on (the roots `AreaLaw.lean`, `AreaLawForMathlib.lean`, `OpenAI.lean` are in `lake exe mk_all` form); the axiom-audit step runs `scripts/audit.lean` instead of the deleted `Arealaw/Audit.lean` |
| `.github/workflows/blueprint.yml` (new, from `blueprint/ci/blueprint.yml`) | `lake build` of the library, then `blueprint/scripts/ci-pages.sh` (patch VersoBlueprint, `lake exe vbp build`, `check_dag.py`), artifact `blueprint-site` |

No workflow refers to `Arealaw/`, `OpenAI/Audit*.lean`, `docs/oai265/` or `HISTORY.md` after
the change.
