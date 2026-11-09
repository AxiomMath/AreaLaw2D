/-! # `lake lint` driver

Runs Batteries' `runLinter` on each module given (by default the `lintDriverArgs` of
`lakefile.toml`), each in its own process. One `runLinter` process imports every module it lints
into the same address space, and two imports of the Mathlib-sized closure of `AreaLaw` and
`AreaLawForMathlib` exceed the memory of a CI runner; one process per module frees it in
between. Arguments starting with `-` (`--update`, `--trace`, `--no-build`) go to every run. The
exit code is nonzero if any run fails. -/

def main (args : List String) : IO UInt32 := do
  let (flags, mods) := args.partition (·.startsWith "-")
  let lake := (← IO.getEnv "LAKE").getD "lake"
  let mut failed : List String := []
  for m in mods do
    let child ← IO.Process.spawn { cmd := lake, args := #["exe", "runLinter"] ++ flags ++ #[m] }
    if (← child.wait) != 0 then failed := failed ++ [m]
  unless failed.isEmpty do
    IO.eprintln s!"lake lint: linting failed for {failed}"
  return if failed.isEmpty then 0 else 1
