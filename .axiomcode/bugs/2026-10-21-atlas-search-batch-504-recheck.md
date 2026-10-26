# Sidecar atlas_search semantic batch returns bare HTTP 504 (Gateway Timeout): duplicate of #12648 / #12651

- Date: 2026-10-21
- Outcome: duplicate (not reproduced on recheck)
- Blame: AxiomMath/axiom capabilities sidecar, capabilities/tools/src/capabilities/tools/atlas.py:114-118 (`_raise_for_status` drops the server's detail) and :287-288 (no retry). Trigger: the atlas-search server's SemanticSearchTimeoutError mapped to 504. Full analysis is in the main checkout's `.axiomcode/bugs/2026-10-20-atlas-search-batch-semantic-504.md`.
- Issue: none new. #12648 is open and already has a comment with the semantic-batch case (https://github.com/AxiomMath/axiom/issues/12648#issuecomment-6300119769). #12651 (axiomcode-v5) covers AxiomCode's part. This occurrence adds nothing new.

## What was done
`mcp__capabilities-sidecar__atlas__atlas_search` with a batch of 3 semantic queries (two workers).

## What came back (verbatim)
atlas-search API returned HTTP 504 (Gateway Timeout)

## Expected
Results, or an error carrying the server's detail, plus a retry on a transient 504.

## Reproduction
Rechecked 2026-10-21 with a 3-query semantic batch (binEntropy concavity, a PSD trace Hölder bound, partial trace PSD), k=3, detail=signature. It returned 200 in seconds. The failure is intermittent.

## Cause
See the 2026-10-20 record and #12648.

## Versions
AxiomCode 0.5.103; the sidecar build is unknown.

## Related issues and PRs
#12648 (open), #12651 (open, axiomcode-v5), #13472 (open, a different symptom).

## Workaround
Retry, or send the queries one at a time or in smaller batches.

## Upstream draft
none
