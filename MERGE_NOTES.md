# Merge notes: v2 candidate

This branch (`ruiz/v2-merge`) merges the restructured proof body of AreaLaw2D-internal
(`main`, commit 65fcc00) into the public repository (v1, `main`, commit 1e91b65, tag `v1.0`),
and restores what v1 has that the restructuring dropped.

Sources:

- v1: public `main`, commit 1e91b65.
- v2: internal `main`, commit 65fcc00.
- 3D: branch `ruiz/3d-targets`, commit 17c87f8. This branch is not on the public remote; it
  exists only as a local branch of the maintainer's clone of the public repository, and was
  fetched from there without modifying it.

## Step 1: merge

`git merge internal/main`. The merge base of the two histories is 1e91b65 itself (v2 was
branched from the tip of v1 and v1 has no later commits), so git applied every v2 change
without a conflict and the merged tree is exactly v2's tree at 65fcc00. No conflict had to be
resolved by hand.

Taken from v2 (all of it, as the merge base had nothing newer):

- `AreaLaw/` (161 files) and `AreaLaw.lean`, `AreaLawForMathlib/` (143 files) and
  `AreaLawForMathlib.lean`: the restructured proof body.
- `blueprint/`, `digest/`, `paper/`, `Map.md`, `RefactoringPlan.md`, `RefactoringResult.md`,
  `scripts/` (including `scripts/audit.lean` and `scripts/lint/`), `.github/workflows/`.
- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` (the Lean and Mathlib pins are
  unchanged at v4.33.0; the manifest gains the local `lintall` package).
- `OpenAI/Statements.lean` with its two first import lines re-pointed (handled again in Step 2).
- `Solution/Basic.lean` re-pointed to `AreaLaw.areaLaw` (see Step 3).
- `docs/StatementAudit.md` with one line changed (see Step 3).
- `README.md` (reworked in Step 5).
- v2's deletions under `OpenAI/` (918 of 919 files; only `Statements.lean` remains) and of
  `Arealaw/` (35 files) and `Arealaw.lean`, accepted for now as instructed.
- v2's deletions of `HISTORY.md`, `docs/oai265/`, `docs/README-quantum-arealaw.md` and
  `docs/charter-quantum-arealaw.md`, all reverted in Step 3.

Taken from v1 at this step: nothing beyond the common history; v1's files that v2 kept
unchanged (`Challenge/`, `Comparator/`, `LICENSE`, `NOTICE`) are identical on both sides.
