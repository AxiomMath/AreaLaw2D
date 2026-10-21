# VersoBlueprint depsClosureComplete (Graph.lean:741) enumerates every DAG path, so vbp build never finishes on a large, fully formalized blueprint

- Date: 2026-10-21
- Outcome: not ours (AxiomCode issue filed; upstream drafted)
- Blame: leanprover/verso-blueprint — src/VersoBlueprint/Graph.lean:741 (`depsClosureComplete`), at v4.33.0 e0d66722 and default branch v4.35.0 5a5bfc7e
- Issue: https://github.com/AxiomMath/axiom/issues/14877 (axiomcode-v5). Nothing posted upstream; the draft is below, waiting for the user.

## What was done
`lake exe vbp build` (VersoBlueprint v4.33.0, Lean 4.33.0) in blueprint/. The blueprint has 221 nodes, all formalized, and 759 acyclic dependency edges.

## What came back (verbatim)
No output. The generator process (`lean .../AreaLawBlueprintMain.lean`) ran for more than 20 CPU-minutes and wrote no site. With 654 edges the same project rendered in about 10 min.

## Expected
Rendering time roughly linear in the size of the graph.

## Reproduction
A Python model of the function on a ladder DAG. It was in scratch, which has been removed; the code is in issue #14877. The model visits 2^(k+1)-2 nodes for k layers: 2,097,150 visits at 40 nodes / 76 edges, against 78 visits with one shared visited set. A DP over the real graph counts about 2.4e10 paths at 759 edges and 3.7e5 at 654 edges. I did not re-run the real build: the brief said not to run lake.

## Cause
In `roots.all fun dep => ... depsClosureComplete ... (visited.insert dep)`, `visited` passes down one path but is not shared across siblings. On a fully formalized DAG nothing short-circuits, so the walk enumerates every path. The function is called once per node (Graph.lean:762, 770, 783, 792, 793). It is unchanged on v4.35.0 (the default branch) and on the draft-PR branch fix/transitive-sorry-status (line 619).
Permalink: https://github.com/leanprover/verso-blueprint/blob/e0d667222e8222ac4bfd74780f69a2e89cd4655f/src/VersoBlueprint/Graph.lean#L741

## Versions
- VersoBlueprint v4.33.0 = e0d667222e8222ac4bfd74780f69a2e89cd4655f; default branch v4.35.0 = 5a5bfc7e17ddba0cbce176d0fe3bfe6a257b16ec
- Lean v4.33.0; verso 36664a0e
- AxiomCode plugin 0.5.103, substrate 0.5.103 (editable /opt/axiomcode/src)

## Related issues and PRs
- leanprover/verso-blueprint: none. I searched open and closed issues and PRs for depsClosureComplete, slow, exponential, performance, transitive and graph. Draft PR #475 (fix/transitive-sorry-status) touches closure checking but keeps the same function.
- AxiomMath: none before this issue. AxiomMath/axiom#14867 (no C compiler for Verso) is a different bug.

## Workaround
Run `blueprint/scripts/patch_versoblueprint.py` before `lake exe vbp build`. It rewrites the function as a worklist with one global visited set. With it the site renders in about 3 min (`vbp check` ok, 682/682).

## Upstream draft
Target: new issue in leanprover/verso-blueprint (none exists). The real reproduction needs a private project; the Python model was run end to end, the Lean build was not re-run here.

Title: `depsClosureComplete` enumerates every path of the dependency DAG (exponential time on large formalized blueprints)

Body:
> `depsClosureComplete` (src/VersoBlueprint/Graph.lean:741, unchanged from v4.33.0 to v4.35.0) threads `visited` down each path but not across the siblings in `roots.all`. When every node is formalized nothing short-circuits, so the walk visits each node once per root-to-node path. That count is exponential in DAG depth: a ladder of k layers of 2 nodes costs 2^(k+1) visits. In a real blueprint with 221 nodes and 759 edges (about 2.4e10 paths) `vbp build` did not finish after 20+ CPU-minutes; with 654 edges (3.7e5 paths) it took about 10 minutes.
>
> Suggested fix: use a worklist with a single visited set for the whole traversal. It gives the same result in O(V+E) per call. Optionally memoise the result per node, since the function is called once per node at lines 762-793. A patched version made the same build finish in about 3 minutes:
> ```lean
> partial def depsClosureComplete (external : ExternalCodeStatus) (state : Environment.State) (mode : DepTraversal)
>     (roots : Array Name) (visited : NameSet := {}) : Bool := Id.run do
>   let mut stack := roots.toList
>   let mut vis := visited
>   while true do
>     match stack with
>     | [] => return true
>     | dep :: rest =>
>       stack := rest
>       if vis.contains dep then continue
>       match state.data.get? dep with
>       | none => return false
>       | some node =>
>         if !nodeLocalFormalized external node then return false
>         vis := vis.insert dep
>         stack := (depsForTraversal mode node).toList ++ stack
>   return true
> ```
