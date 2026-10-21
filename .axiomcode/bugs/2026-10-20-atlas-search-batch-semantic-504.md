# Sidecar atlas_search (semantic batch) relays a server 504 as a bare "HTTP 504 (Gateway Timeout)", dropping the server's detail and not retrying

- Date: 2026-10-20
- Outcome: commented (duplicate of open issues; new evidence added). Not reproduced on retry (0 of 3).
- Blame: AxiomMath/axiom capabilities sidecar — capabilities/tools/src/capabilities/tools/atlas.py:114-118 (`_raise_for_status` drops body) and :287-288 (`batch_search` single post, no retry) at ab7d9758ee. Trigger: atlas-search server SemanticSearchTimeoutError (k-NN or hydrate checkout over db_checkout_budget) -> 504 at atlas/services/atlas_search/server/routes/search.py:1423 (def09bf0d9); retriever.py:1394/:3231 (290d7354be). AxiomCode part: acp_server.py _HOSTED_PROMPT (~L250-266) routes agents to sidecar Atlas tools with no word on reading 503/504 (already #12651).
- Issue: commented https://github.com/AxiomMath/axiom/issues/12648#issuecomment-6300119769 ; AxiomCode side already tracked in https://github.com/AxiomMath/axiom/issues/12651 (open, axiomcode-v5; its 2026-10-20 comment already covers batch 504) — no new comment there, nothing new for AxiomCode's part.

## What was done
`mcp__capabilities-sidecar__atlas__atlas_search` batch mode (`queries`), semantic, default corpora/detail, two queries:
"For a real number x and an exponent y with 0 ≤ y ≤ 1/2, the real power x ^ y is nonnegative even when x is negative." and
"If for every epsilon > 0 eventually in n a family … then the supremum over i tends to zero." (s07-energy worker, ~19:30 UTC).

## What came back (verbatim)
atlas-search API returned HTTP 504 (Gateway Timeout)

## Expected
Results per query, or an error that carries the server's detail (which index/phase exceeded which budget) and a retry on a transient 504.

## Reproduction
Not reproduced, ~19:52 UTC: (1) same 2-query batch, k=5, detail="signature" -> 200; (2) single query 1 -> 200; (3) same batch, k=2, default detail -> 200. All returned within seconds. Intermittent; matches prior reports (1 of N batch calls).

## Cause
- Server: in semantic mode the only IndexedSearchTimeoutError is SemanticSearchTimeoutError ("knn" at retriever.py:1394, "hydrate" at :3231, budget db_checkout_budget_seconds), mapped to 504 with detail at search.py:1423. nginx proxy_read_timeout 60s > client 30s, so the 504 is app-generated (inferred; no server logs).
- Client (sidecar): `_raise_for_status` logs resp.text but raises only status + reason phrase; batch_search has no retry.

## Versions
AxiomCode 0.5.103 (plugin.json 0.5.103, axiomcode.__version__ 0.5.103, /opt/axiomcode/src). Sidecar build unknown from session; code read at main ab7d9758eede856738ff37e8d17b100338893cd5 (capabilities/tools/.../atlas.py). Server code at def09bf0d9 (routes/search.py), 290d7354be (retriever.py).

## Related issues and PRs
- AxiomMath/axiom#12648 (open): same `_raise_for_status` defect; comments already cover glob/grep 504 and glob batch 504. Commented with the semantic-batch case.
- AxiomMath/axiom#12651 (open, axiomcode-v5): AxiomCode hosted note silent on sidecar 503/504. Covers this.
- AxiomMath/axiom#13472 (open): client 30 s read timeout ("atlas-search timed out") — different symptom.
- AxiomMath/axiom#10263, #12590, #12592, #13506: neighbouring atlas/sidecar issues, not duplicates.

## Workaround
Retry the call; if a batch 504s, resend the queries individually or in smaller batches. A 504 here is a transient server budget overrun, not an outage.

## Upstream draft
none (all responsible code is in AxiomMath/axiom)
