# Port brief: the TNLean Proposition 10.2 cone into quantum-arealaw

Repository: /root/dev/quantum-arealaw-ba5d4fde (branch agents/ba5d4fde-fa2b-5470-b436-3528b6b8158b).
Read /root/dev/quantum-arealaw-ba5d4fde/CLAUDE.md first: its conventions bind every file you
write.  The campaign plan, with the whole cone and every target module name, is
docs/oai265/Prop102Plan.md.

Goal of the campaign: Proposition 10.2 (`OpenAI.amplification`, OpenAI/Statements.lean) of
OAI265, ported from TNLean, which proves it (`TNLean.PEPS.AreaLaw.amplificationBound`,
`TNLean/PEPS/AreaLaw/AmplificationProof.lean:103`).  The charter: "Port TNLean file by file at
v4.33 with attribution, only along a spine theorem's cone."

## Sources (read-only clones; never edit them)

- TNLean `834d8da300df206ff8f2e659cfc2f8a478c759ad`: .axiomcode/scratch/amp/tnlean/
- QICLean `ed700e7b45ffea4379e980b222094136800de55e` (TNLean's pin): .axiomcode/scratch/amp/qiclean/
- Paper TeX: .axiomcode/scratch/amp/oaimath/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/
  (`09-amplification.tex` is Section 10; file numbers are one less than section numbers).
- docs/oai265/ports/PortMap.txt: `<source path> <OpenAI module>` for the files this repository
  already ports, and NOTE lines with the encoding renamings.  A source module listed there, or
  named in a `Ported from` header under OpenAI/, is ALREADY in the repository: import the OpenAI
  module, never port it again.  The older ports came from older revisions; if a declaration you
  need is missing or differs there, add the minimal missing lemma to YOUR file (and say so in
  your report), never edit the existing module.

## Names

- `TNLean.PEPS.AreaLaw.Amplification.X` -> `OpenAI/Amplification/X.lean`, module
  `OpenAI.Amplification.X`; other `TNLean.PEPS.AreaLaw.X` -> `OpenAI/X.lean`;
  `TNLean.Circuit.LiebRobinson.X` -> `OpenAI/LiebRobinson/X.lean`; `TNLean.Circuit.X`,
  `TNLean.Algebra.X`, `QICLean.<Dir>.X` -> `OpenAI/X.lean`.
- Namespace `TNLean.PEPS.AreaLaw` -> `OpenAI` (and `.Exponents` -> `OpenAI.Exponents`); QICLean
  namespaces (`PoissonWord`, `Entropy`, `FiniteProduct`, `Matrix`, ...) are kept as the
  existing ports keep them.  Declaration names otherwise unchanged, so later ports line up.
- Header: the source's Apache-2.0 copyright block, then
  `Ported from LionSR/TNLean commit 834d8da300df206ff8f2e659cfc2f8a478c759ad,`
  `` `<source path>` (Apache 2.0). `` (QICLean: `ed700e7b45ffea4379e980b222094136800de55e`),
  followed by every adaptation (encodings, renamed dependencies, omitted declarations).  The
  pure files already copied carry the first two lines; add adaptations as you make them.

## Rules

1. Statements are the source's, verbatim up to the renamings and encodings of this brief and
   Lean/Mathlib v4.33 spelling.  Never weaken one.  If a statement cannot be ported as is, stop
   on that declaration and say exactly why in your report.
2. No `sorry` (unless your task is explicitly a statement freeze), no `axiom`, no
   `native_decide`, no `admit`.  Every file you finish must pass `axle_check` with no errors and
   no disallowed axioms; run `axiom_audit` on its main theorems.
3. Never `import Mathlib`.  Import the specific Mathlib modules and the narrowest OpenAI
   modules you need (the copied files import every module a source dependency maps to; prune
   what you do not use).
4. Never introduce a parallel encoding of something the repository already has.  Operator
   support is `OpenAI.IsSupportedOn` (bridge to TNLean's span: `OpenAI.isSupportedOn_iff_mem_span`),
   conditional expectation is `OpenAI.condExpect` (TNLean `siteExpectation q (graphBall
   (domainGraph Λ) x l)` is `condExpect (graphNbhd_subset Λ {x} l)`), `Arealaw.extendId` is TNLean
   `embedOp`/`localLift`, strong subadditivity is `Arealaw.vonNeumann_strong_subadditivity`,
   QICLean `vonNeumannEntropy` is `Arealaw.vonNeumann`, `partialTraceLeft/Right` are Physlib
   `Matrix.traceLeft/traceRight`, `Matrix.traceDistance ρ σ` is `(ρ - σ).traceNorm / 2`,
   `IsIsometry` is Physlib `Matrix.Isometry` (PortMap.txt NOTE lines list the rest).  The lattice
   model follows OpenAI/LatticeConstraints.lean and OpenAI/Scan/TargetTypicalWindow.lean: TNLean
   `Site Λ` is `↥(Λ : Set (ℤ × ℤ))` or a point of `ℤ × ℤ` in `Λ`, `LocalHamiltonian Λ q R J` is an
   interaction `Φ` with `OpenAI.IsAdmissible Λ R J Φ` (operator `hamiltonian Λ Φ`, term
   `extendId _ (Φ X)`), `AdmissibleSupport Λ R` is `supports Λ R`, `IsGappedGroundState` is
   `‖Ω‖ = 1`, the eigen-equation and `OpenAI.HasGlobalGap` for `Ω : EuclideanSpace ℂ
   (Reg (Qudits q) Λ)`, `graphNeighborhood Λ r S` is `OpenAI.graphNbhd Λ S r`, the unordered
   `edgeBoundary` is the ordered `OpenAI.edgeBoundary`, `boundaryEndpoints` is
   `OpenAI.cutEndpoints`.  Search the repository (Grep over OpenAI/ and Arealaw/) and
   `mathlib_search` before porting any helper.
5. Write ONLY the files assigned to you.  Never edit another file, `OpenAI.lean` (generated
   umbrella), `OpenAI/Audit.lean`, `OpenAI/Statements.lean`, anything under `Arealaw/`.  Do not
   commit, push, or build the whole library; the coordinator does those.  Scratch only in your
   own `.axiomcode/scratch/amp/<your task id>/` (create it, remove it at the end); never use
   `Arealaw/Probe.lean`.  Checks go through the hosted Lean session (`lean_diagnostic_messages`,
   `axle_check`); there is no local build in this checkout.
6. Docstrings: every definition and main theorem keeps (or gets) one; keep the source's paper
   citations; no LLM prose (CLAUDE.md).

## Report back

- each file written, by path, with its main declarations `name file:line`;
- `axle_check` result per file and `axiom_audit` output quoted exactly;
- every adaptation (renamed dependency, added helper, changed spelling, changed encoding) by
  declaration;
- anything you could not port, stated plainly; any tool bug, on a line starting `BUG:`.
