#!/usr/bin/env python3
"""Patch VersoBlueprint's dependency-closure check (src/VersoBlueprint/Graph.lean) before a build.

`depsClosureComplete` (VersoBlueprint v4.33.0 and main, Graph.lean:741) walks the dependency
graph with a visited set that is passed down one path but not across siblings, so it visits every
path of the DAG: about 2.4e10 paths for this blueprint's 759 edges, so the site generator never
finishes. The patch keeps the visited set across the whole walk (the same answer: every reachable
dependency is present and formalized). Idempotent; run from blueprint/ before `lake exe vbp build`.
"""
import os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
P = os.path.normpath(os.path.join(HERE, '../../.lake/packages/VersoBlueprint/src/VersoBlueprint/Graph.lean'))

OLD = '''partial def depsClosureComplete (external : ExternalCodeStatus) (state : Environment.State) (mode : DepTraversal)
    (roots : Array Name) (visited : NameSet := {}) : Bool :=
  roots.all fun dep =>
    if visited.contains dep then
      true
    else
      match state.data.get? dep with
      | none => false
      | some node =>
        if !nodeLocalFormalized external node then
          false
        else
          let visited := visited.insert dep
          depsClosureComplete external state mode (depsForTraversal mode node) visited
'''

NEW = '''partial def depsClosureComplete (external : ExternalCodeStatus) (state : Environment.State) (mode : DepTraversal)
    (roots : Array Name) (visited : NameSet := {}) : Bool := Id.run do
  -- patched (AreaLaw blueprint, scripts/patch_versoblueprint.py): one visited set for the whole
  -- walk, so each dependency is checked once instead of once per path
  let mut stack := roots.toList
  let mut vis := visited
  while true do
    match stack with
    | [] => return true
    | dep :: rest =>
      stack := rest
      if vis.contains dep then continue
      match state.data.get? dep with
      | none => return false
      | some node =>
        if !nodeLocalFormalized external node then return false
        vis := vis.insert dep
        stack := (depsForTraversal mode node).toList ++ stack
  return true
'''

if not os.path.exists(P):
    sys.exit(f'patch_versoblueprint: {P} not found (run `lake update` / a first build in blueprint/)')
s = open(P).read()
if NEW in s:
    print('patch_versoblueprint: already patched')
elif OLD in s:
    open(P, 'w').write(s.replace(OLD, NEW))
    print('patch_versoblueprint: patched', P)
else:
    sys.exit('patch_versoblueprint: depsClosureComplete changed upstream; review the patch')
