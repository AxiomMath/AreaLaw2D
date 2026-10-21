# axile-session: calls whose client timed out stay queued behind the per-(root,lane) lock and still run (livelock under retries)

- Date: 2026-10-20
- Outcome: filed
- Blame: AxiomMath/axiom (agents/definitions/base/sidecar/axile-session/server.py:141) — not pinned beyond the lock; Axile server itself not at fault
- Issue: https://github.com/AxiomMath/axiom/issues/14633

## What was done
About six sibling subagents called mcp__axile__diagnostics concurrently on Movement/*.lean in worktree agent-a60a373f645c502ce, retrying on timeout.
## What came back (verbatim)
"mcp__axile__diagnostics is livelocked for worktree agent-a60a373f (lane queue ~210 s per /tmp/axile-mcp.log, every call times out client-side while the server still runs it; all six Movement/* siblings retry, so the queue keeps growing)."
## Expected
Server drops/coalesces calls of timed-out clients, or answers busy early.
## Reproduction
Not re-run (told not to add load). Log analysis: 180 calls, 2199 s serialised op time, 147 with queue>60 s, all outcome ok, none cancelled.
## Cause, Versions, Related issues and PRs
See the issue body below (same text as filed). Related: axiom#12725 (open, 60 s cap), #12726 (closed), axile#3329 (unrelated).
## Workaround
Do not retry a timed-out call; wait (the server is still running it) and serialise calls per worktree, one agent per root.
## Upstream draft
none

---- filed body ----
**Upstream defect:** AxiomMath/axiom `agents/definitions/base/sidecar/axile-session/server.py` (this issue) — AxiomCode's part: the hosted prompt should tell agents that a timed-out `mcp__axile__*` call is still running server-side and must not be retried in parallel; the maintainer routes the rest.

**What happens.** The sidecar serialises every call of a (project root, lane) behind one `asyncio.Lock`, and a call whose client has timed out is still queued and still runs to completion. Agents retry on timeout, so the queue grows faster than it drains: a livelock where every call times out.

**Reproduction.** Not re-run (no extra load launched); from the live `/tmp/axile-mcp.log` (server.py identical to main @ a923d7d1e3cf). Six sibling subagents in worktree `agent-a60a373f645c502ce` call `mcp__axile__diagnostics` on `AreaLawRefactored/S05_Conditional/Movement/*.lean` (7 files, ~10 s per call), each retrying after the client's 60 s cut. Any N>=3 parallel callers on one root with per-call time >= 60/N s reproduce it.

**Actual.** For that root, Movement/* only: 180 calls, 2199 s of serialised operation time, 25-34 calls per file; every one `"outcome":"ok"`; 147 of 180 had `queue_ms` > 60000 (the client had already given up, the result was discarded); max `queue_ms` 273733. Other roots in the same log show the same: a3a88da1 max 355918 ms, a6375c7d 391065 ms, 0 calls cancelled (no cancellation anywhere in the log).
```
{"lane":"agent","root":".../agent-a60a373f645c502ce","path":".../Movement/LogMomentsMatrix.lean","outcome":"ok","queue_ms":217705,"open_ms":0,"mirror_ms":161,"operation_ms":18164}
```

**Expected.** A call whose client is gone is dropped before it takes the lock (or cancelled), or identical pending calls (same root, lane, operation, path, range, same file identity) are coalesced onto one run; or the server answers "queued/busy, call again" early so the client has something to wait on. A client timeout must not leave work queued that delays later calls.

**Cause.** `Session.call` does `async with self._lock:` at [server.py:141](https://github.com/AxiomMath/axiom/blob/a923d7d1e3cf/agents/definitions/base/sidecar/axile-session/server.py#L141) (lock created at L127), then runs open, mirror and the operation to completion with no check that the request is still wanted. With `stateless_http=True, json_response=True` (L463-464) nothing signals the handler when the client disconnects, so the abandoned waiters never get cancelled and each one runs its full 5-30 s after its client left. `Projects.call` (L309-336) adds no dedup. Fix sketch: key in-flight calls by (root, lane, operation, path, args) and share the future (coalesce), with a bounded queue depth that returns a "busy, call again" result; and record the request's deadline to skip expired waiters.

**Versions.** server.py identical to AxiomMath/axiom main @ a923d7d1e3cf (file last changed d1e936f7366c). /usr/local/lib/axile-session/server.py in the sandbox.

**Related.** #12725 (open; json_response sends no headers so the 60 s cap cuts calls; its second comment, point 3, noticed the lock queueing but proposes only streaming/early return); #12726 (closed, client timeout config). #3329 in AxiomMath/axile is the unrelated open_workspace copy bug. Fixing #12725 alone would not stop duplicate abandoned work from retries.
