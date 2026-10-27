# Blueprint

The Verso blueprint of the formalization: one chapter per paper section
(`AreaLawBlueprint/Chapters/`), one node per digest anchor with a Lean declaration, labelled by
the anchor id (`D<section>.<n>`), with `(lean := …)` naming the declaration.

Build the library first, then the blueprint:

```bash
lake build                      # at the repository root
cd blueprint
./scripts/ci-pages.sh           # lake exe vbp build + checks; site in _out/site/html-multi/
```

`scripts/check_dag.py` compares the rendered dependency graph with the DAG of
`digest/00-overview.md` §2.1. `scripts/patch_versoblueprint.py` patches VersoBlueprint's
dependency-closure walk, which is exponential in the number of paths of the graph.
The CI job is `.github/workflows/blueprint.yml` in the repository root.
