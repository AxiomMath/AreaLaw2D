# mcp__axile__diagnostics times out: one cold-build call holds the axile-session lane lock for 638-688 s and everything else queues (dup of #14633, new evidence commented)

- Date: 2026-10-21
- Outcome: commented
- Blame: AxiomMath/axiom, agents/definitions/base/sidecar/axile-session/server.py:141 (`Session.call` holds the per-(root, lane) lock for the whole operation; there is no early answer and no drop of a waiter that has timed out)
- Issue: https://github.com/AxiomMath/axiom/issues/14633#issuecomment-6304579774

## What was done
`mcp__axile__diagnostics(path=<worktree>/AreaLawRefactored/S07_Transport/Proposition.lean, start_line=1, end_line=20)`. Then three more calls on other files, and the root `AreaLawRefactored.lean` (twice).

## What came back (verbatim)
The operation timed out.

## Expected
A result, or an early "building, call again".

## Reproduction
Not re-run, to avoid adding load. This is from /tmp/axile-mcp.log (407 calls on this root). Excerpts:
- Proposition.lean: `queue_ms 0`, `operation_ms 637642`.
- Components.lean: `queue_ms 0`, `operation_ms 688205`.
- Later calls had `queue_ms` 400952 (Setup), 636043 (Labels), and 678448 (RoughUpper, operation 13803 ms).

## Cause
The first check of a file whose upstream modules have not been elaborated in the session builds them inside the call. That held the lane lock for over 10 minutes. Every other call on the root waited behind it past the client's cut, and the waiters were never dropped.

## Versions
AxiomCode 0.5.103. The sidecar server is as recorded in #14633: main a923d7d1e3cf.

## Related issues and PRs
#14633 (open; same lock, filed by a worker yesterday, local record in the main checkout `.axiomcode/bugs/2026-10-20-axile-session-abandoned-calls-livelock.md`), #12725 (open; json_response, 60 s cap), #12726 (closed).

## Workaround
Make one call first and wait for it (it keeps running after the client gives up). Then issue the other calls serially, one agent per worktree root.

## Upstream draft
none
