# umbrella_sync (mk_all route) overwrites umbrella docstrings and a hand-curated root without warning, then reports 'clean ... as generated'

- Date: 2026-10-20
- Outcome: filed
- Blame: AxiomMath/axiom (axiomcode-v5) — agents/definitions/axiomcode/v5/src/axiomcode/umbrella.py:797-800 (sync never calls inspect before _generate); registry.py:1091/1108 (reply scans after the overwrite). Line numbers are at main 5f09e61.
- Issue: https://github.com/AxiomMath/axiom/issues/14752

## What was done
umbrella_sync was called with no arguments (root /root/dev/AreaLaw2D-internal-18b3b627) after adding AreaLawForMathlib/QuantumInfo/StateToComplex.lean.

## What came back (verbatim)
{"ok": true, "detail": "No update necessary; No update necessary; No update necessary; No update necessary; Updating 'AreaLawRefactored.lean'; Updating 'AreaLawForMathlib.lean'", "changed": ["AreaLawRefactored.lean","AreaLawForMathlib.lean"], "route": "lake exe mk_all --lib Arealaw && lake exe mk_all --lib OpenAI && lake exe mk_all --lib Challenge && lake exe mk_all --lib Solution && lake exe mk_all --lib AreaLawRefactored && lake exe mk_all --lib AreaLawForMathlib", "umbrellas": [... {"file": "AreaLawRefactored.lean","imports": 139,"clean": true,"summary": "AreaLawRefactored.lean: 139 imports, sorted, nothing else — as generated"}, {"file": "AreaLawForMathlib.lean","imports": 106,"clean": true,"summary": "AreaLawForMathlib.lean: 106 imports, sorted, nothing else — as generated"}]}

On disk, AreaLawRefactored.lean (10 curated section-root imports plus a docstring) became 139 imports with no docstring. AreaLawForMathlib.lean lost its docstring and was re-sorted.

## Expected
Before it runs the generator, `sync` should run `inspect` on each umbrella. If an umbrella has stray lines (a docstring or declarations) or foreign imports, `sync` should refuse to regenerate that file, or keep the content, and say so. It should never say "as generated" over content it has just deleted. The `umbrellas` report should describe the state before the sync, or both states. A root that imports a strict subset of the library's modules, rather than every module, is a sign the root is hand-curated, much as in #13611. Overwriting that root with every module changes what the library exports, and it should at least be flagged.

## Reproduction
No Lean needed. A shell script stands in for `mk_all` and writes what `mk_all` writes. This was run end to end on 0.5.103:
```
P=$(mktemp -d); mkdir -p $P/Lib/A; cd $P
printf '[[lean_lib]]\nname = "Lib"\n' > lakefile.toml
touch Lib/A/X.lean Lib/A/Y.lean Lib/B.lean
cat > Lib.lean <<'EOF'
import Lib.A.X
import Lib.B

/-!
# Curated root

Hand-written prose.
-/
EOF
cat > fake_mk_all.sh <<'EOF'
#!/bin/sh
printf 'import Lib.A.X\nimport Lib.A.Y\nimport Lib.B\n' > Lib.lean
echo "Updating 'Lib.lean'"
EOF
chmod +x fake_mk_all.sh
axc python - <<'PY'
from pathlib import Path; from axiomcode import umbrella as u
r=Path('.')
print("BEFORE", [(d.clean, d.summary()) for d in u.scan(r)])
print("SYNC  ", u.sync(r, command=("./fake_mk_all.sh",)))
print("AFTER ", [(d.clean, d.summary()) for d in u.scan(r)])
PY
```

## Actual output
```
BEFORE [(False, 'Lib.lean: 4 line(s) that `lake exe mk_all --module` would delete — carries a module docstring')]
SYNC   SyncResult(ok=True, detail="Updating 'Lib.lean'", changed=['Lib.lean'], route='./fake_mk_all.sh --lib Lib')
AFTER  [(True, 'Lib.lean: 3 imports, sorted, nothing else — as generated')]
```
Real MCP reply (trimmed):
```
{"ok": true, "detail": "No update necessary; ...; Updating 'AreaLawRefactored.lean'; Updating 'AreaLawForMathlib.lean'", "changed": ["AreaLawRefactored.lean","AreaLawForMathlib.lean"], "route": "lake exe mk_all --lib Arealaw && ... && lake exe mk_all --lib AreaLawForMathlib", "umbrellas": [... {"file": "AreaLawRefactored.lean","imports": 139,"clean": true,"summary": "AreaLawRefactored.lean: 139 imports, sorted, nothing else — as generated"}, {"file": "AreaLawForMathlib.lean","imports": 106,"clean": true,"summary": "AreaLawForMathlib.lean: 106 imports, sorted, nothing else — as generated"}]}
```

Pre-sync scan of the real f372e84 umbrellas, copied into scratch:
```
False AreaLawRefactored.lean: 6 line(s) that `lake exe mk_all --module` would delete — carries a module docstring
False AreaLawForMathlib.lean: 5 line(s) that `lake exe mk_all --module` would delete — carries a module docstring
```

## Cause
- [`umbrella.py#L797-L800`](https://github.com/AxiomMath/axiom/blob/5f09e618c0646f81311a7aaa28f894f4dfef78a7/agents/definitions/axiomcode/v5/src/axiomcode/umbrella.py#L797-L800) (`sync`) calls [`_generate`](https://github.com/AxiomMath/axiom/blob/5f09e618c0646f81311a7aaa28f894f4dfef78a7/agents/definitions/axiomcode/v5/src/axiomcode/umbrella.py#L839) and never calls `inspect`/`scan` first. `_generate` runs `mk_all` on every library, which rewrites the whole file. Its only post-check, at [L895-L898](https://github.com/AxiomMath/axiom/blob/5f09e618c0646f81311a7aaa28f894f4dfef78a7/agents/definitions/axiomcode/v5/src/axiomcode/umbrella.py#L895-L898), is `style_note`.
- [`registry.py#L1091`](https://github.com/AxiomMath/axiom/blob/5f09e618c0646f81311a7aaa28f894f4dfef78a7/agents/definitions/axiomcode/v5/src/axiomcode/registry.py#L1091) and [`#L1108`](https://github.com/AxiomMath/axiom/blob/5f09e618c0646f81311a7aaa28f894f4dfef78a7/agents/definitions/axiomcode/v5/src/axiomcode/registry.py#L1108) (`umbrella_sync_tool`) compute `umbrellas` with `umbrella_mod.scan(target)` **after** `umbrella_mod.sync(target)`. The detector ([`inspect`, L479](https://github.com/AxiomMath/axiom/blob/5f09e618c0646f81311a7aaa28f894f4dfef78a7/agents/definitions/axiomcode/v5/src/axiomcode/umbrella.py#L479)) therefore only ever sees the regenerated file. That contradicts the tool description at [L1084](https://github.com/AxiomMath/axiom/blob/5f09e618c0646f81311a7aaa28f894f4dfef78a7/agents/definitions/axiomcode/v5/src/axiomcode/registry.py#L1084).
- The reconstruct route (`_reconstruct`/`reconcile`) keeps non-import lines byte for byte, so only the generator route destroys content.
- Possible fix: in `sync`, take `drift = {p: inspect(root, p) for p in umbrellas(root)}` before `_generate`. For a library whose umbrella has `stray_lines` or `foreign_imports`, either use `reconcile` (which keeps them) instead of `mk_all`, or refuse with the summary. Report the pre-sync drift in the reply.

## Versions
- Installed: axiomcode 0.5.103 (editable, /opt/axiomcode/src, not a git checkout). Plugin plugin.json 0.5.103 (the two match).
- Checked `main` at 5f09e618c0646f81311a7aaa28f894f4dfef78a7 (0.5.105, 2026-10-20). The defect is unchanged there. The line numbers above are at that commit.

## Related issues and PRs
- #13611 (open): `umbrellas` treats a hand-maintained root as mk_all-generated, and `pre_pr_gate` advises `umbrella_sync` on it. Same root assumption; this issue covers the destructive half.
- #13823 (closed): the Axile route of `sync` never consults `inspect` (merge markers). Same "sync ignores its own scan" shape, on the other route.
- #13944 (closed): `Drift.clean` says "as generated" while modules are missing.
No PRs found.

## Workaround
Run `git checkout` on the umbrellas and add the new import line by hand, which is what the main thread did. Before running umbrella_sync on a project with a local build, check `umbrella.scan` first. If any umbrella is clean:false (it carries prose), do not run umbrella_sync.

## Upstream draft
none
