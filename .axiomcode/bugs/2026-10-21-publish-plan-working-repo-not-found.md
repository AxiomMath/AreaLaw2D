# publish_plan refuses and challenge_authored reads "unknown" on AreaLaw2D-internal: the repo is misclassified as published (same root cause as #14768)

- Date: 2026-10-21
- Outcome: commented (this is a duplicate of #14768's root cause, with new consequences added)
- Blame: AxiomMath/axiom (AxiomCode). The cause is `src/axiomcode/publish.py:3792` `is_publication`, together with `charter.py:316` `has_charter_file`, which counts only dashboard.toml. Consequences: `publish.pair` returns working=None, and `challenge.provenance` (challenge.py:531) skips the recorded `challenge_authored`.
- Issue: https://github.com/AxiomMath/axiom/issues/14768#issuecomment-6308673922

## What was done
`publish_plan()`, `publish_comparator_lint()` and `charter()`, all with no arguments, in session project /root/dev/AreaLaw2D-internal-18b3b627.

## What came back (verbatim)
publish_plan: {"error": "/root/dev/AreaLaw2D-internal-18b3b627 is a published repo, and the repo it was published from was not found (neither the session's project nor a chartered sibling without `-publish`): name it as `root`.", "project_root": "/root/dev/AreaLaw2D-internal-18b3b627"}
publish_comparator_lint and charter, each: "challenge_authored": {"by": "unknown", "why": "a published repo, whose history begins at publication and says nothing about who wrote the challenge, and its working repo was not found"}
The charter() semantic block says "challenge_authored": "human", with elicited: true.

## Expected
publish_plan should return the comparator host panel, and challenge_authored should be "human".

## Reproduction
`axc python -c "from pathlib import Path; from axiomcode import publish, charter; r=Path('.').resolve(); print(publish.is_publication(r), charter.has_charter_file(r))"` in the project prints `True False`. Comparator/comparator.json exists and there is no dashboard.toml.

## Cause
- `is_publication` decides that any repo without a dashboard.toml charter and with Comparator/comparator.json is published.
- `pair()` then finds no working repo. The session is the same root, and the name has no `-publish` suffix.
- `provenance` returns "" before it reads `charter.semantic.challenge_authored`.
- The elicited semantic charter is served from the MCP server's in-memory cache. `.axiomcode/charter.toml` is no longer on disk. `_LiveCharter` stamps only dashboard.toml (#13497).

## Versions
- AxiomCode plugin and substrate 0.5.103 (editable /opt/axiomcode/src)
- AxiomCode main 5f09e618c0: `is_publication` is unchanged there

## Related issues and PRs
- #14768 (open): the same root cause. Commented there.
- #13497 (open): stale charter cache.
- #12587 and #12589 (closed): related misclassifications, not duplicates.

## Workaround
`axc publish` in Bash prints the panel (route axile). Take challenge_authored = human from the charter's semantic block or from RefactoringPlan.md.

## Upstream draft
none
