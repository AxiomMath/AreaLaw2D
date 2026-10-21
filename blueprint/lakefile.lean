import Lake
open Lake DSL

/-!
The blueprint of the area-law formalization: a Verso Blueprint project laid out as
verso-blueprint's `project_template/` (branch `v4.33.0`).

It is a Lake package of its own, so the main `lakefile.toml` and its targets are unchanged.
The chapters name the declarations of the main library (`(lean := "AreaLaw.…")`), so the
main package is required by path and its packages directory is shared: build the main
library first (`lake build` at the repository root), then the blueprint
(`lake exe vbp build` here), which compiles only Verso and the chapters.

The last `require` wins a version conflict, so the main package comes last: VersoBlueprint
asks for ProofWidgets `v0.0.104`, Mathlib (and so the built main library) for its own.
-/

require VersoBlueprint from git "https://github.com/leanprover/verso-blueprint"@"v4.33.0"
require arealaw from ".."

package AreaLawBlueprint where
  packagesDir := "../.lake/packages"
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target]
lean_lib AreaLawBlueprint where
