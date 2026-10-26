# A two-dimensional area law from a global spectral gap, in Lean 4

A Lean 4 formalization of *A two-dimensional area law from a global spectral gap*
(`paper/paper.pdf`, LaTeX in `paper/sections/`).

## What is proved

The paper's results are stated as `def … : Prop` in `OpenAI/Statements.lean`, for every
`RCLike` scalar field `𝕜`, and each is proved:

| Paper | Statement | Lean proof |
| --- | --- | --- |
| Theorem 1.1 (area law) | `OpenAI.AreaLaw` | `AreaLaw.areaLaw` |
| Corollary 1.2 | `OpenAI.AreaLawCorollary` | `AreaLaw.areaLawCorollary` |
| Lemma 2.1 | `OpenAI.ConditionalContinuity` | `AreaLaw.conditionalContinuity` |
| Lemma 3.1 | `OpenAI.MarginalTails` | `AreaLaw.marginalTails` |
| Lemma 3.2 | `OpenAI.BufferDiscount` | `AreaLaw.bufferDiscount` |
| Proposition 3.3 | `OpenAI.InitialBoxEstimate` | `AreaLaw.initialBoxEstimate` |
| Proposition 4.3 | `OpenAI.PositiveReplacement` | `AreaLaw.positiveReplacement` |
| Proposition 9.6 | `OpenAI.CollarBound` | `AreaLaw.Scanner.prop_9_6`, `AreaLaw.collarBound_of_complex` |
| Proposition 10.2 | `OpenAI.Amplification` | `AreaLaw.amplification` |
| Lemma 11.1 | `OpenAI.TwoFamilyCancellation` | `AreaLaw.twoFamilyCancellation` |
| Proposition 11.2 | `OpenAI.TwoFamilyDecomposition` | `AreaLaw.Geometry.prop_11_2` |

There is no `sorry` outside `Challenge/`, and every result depends only on the axioms
`propext`, `Classical.choice` and `Quot.sound`.

`OpenAI/Statements3D.lean` fixes statements for a three-dimensional continuation, explained in
`docs/3D/Targets.md`. One of them is proved: the area law on cylinders `Λ' × [0, h)` over a
planar domain (`OpenAI.cylinderAreaLaw3D`, `OpenAI.cylinderAreaLawOfPlanar3D`), as a corollary of
Theorem 1.1.

## The tree

| Path | Content |
| --- | --- |
| `OpenAI/Statements.lean` | The statements: lattice domains, admissible Hamiltonians, the global gap, the edge boundary, and the results above as `def … : Prop`. Imports only Mathlib, Physlib and `AreaLawForMathlib`. Frozen on October 13, 2026; since then only the proof stubs were removed and, in the restructuring, the two import lines were re-pointed to the new homes of the same definitions. |
| `AreaLaw/` | The proof, one module per paper section: `S01_AreaLaw`, `S02_Preliminaries`, `S03_InitialBox`, …, `S11_Geometry`; larger sections are split by subsection. Declarations are named by paper number (`lemma_6_4`, `prop_9_6`, `step_11_26_3`) and proof steps carry their digest ids (`-- D6.4.2`). The development is over `ℂ`; `AreaLaw/Transfer.lean` proves each `RCLike 𝕜` statement from its `ℂ` instance. |
| `AreaLawForMathlib/` | Results Mathlib and Physlib lack, in Mathlib's layout (`Analysis/Matrix/`, `RepresentationTheory/SchurWeyl/`, `QuantumInfo/`, …); each file names the Mathlib or Physlib file it extends. `QuantumInfo/Region/` holds the region encoding the statements use: configurations `Reg`, the partial trace `ptrace`, states `SubState`/`MState`, `regionEntropy`, `mutualInfo`, the trace distance. |
| `OpenAI/Statements3D.lean`, `OpenAI/Cylinder3D.lean` | The three-dimensional statements and the cylinder area law. `OpenAI/Cylinder3DSupport.lean` restores the lemmas of v1 the cylinder proof uses. |
| `OpenAI/Audit.lean`, `OpenAI/Audit3D.lean`, `scripts/audit.lean` | `#print axioms` of every frozen statement's proof, of the 3D theorems, and of every result of the v1 audit that still exists. |
| `digest/` | The paper digest: one file per section, every result, definition and proof step with an anchor `D<section>.<n>`. |
| `Map.md` | Anchor → Lean declaration, with file and line, and the faithfulness of v1 against each anchor. |
| `blueprint/` | The Verso blueprint (below). |
| `Challenge/`, `Solution/`, `Comparator/` | The comparator pair for Theorem 1.1 (below). |
| `RefactoringPlan.md`, `RefactoringResult.md` | The structure the code follows, and the record of route differences from the paper, constants and digest corrections. |
| `docs/StatementAudit.md` | Clause-by-clause comparison of `OpenAI/Statements.lean` with the paper. |
| `HISTORY.md`, `docs/oai265/` | The history of v1 and its working record (plan, inventory, decisions, one plan per proposition), kept as an archive; they describe the v1 tree. |
| `MERGE_NOTES.md` | What the v2 candidate took from v1 and from the restructuring. |

## Building and verification

Lean `v4.33.0`, Mathlib `v4.33.0`, [Physlib](https://github.com/leanprover-community/physlib)
at the commit pinned in `lake-manifest.json`.

```bash
lake exe cache get
lake build
lake env lean scripts/audit.lean     # axioms of each frozen statement's proof
lake env lean OpenAI/Audit.lean      # the same, the 3D theorems and the v1 audit
lake env lean OpenAI/Audit3D.lean    # axioms of the 3D theorems
lake exe mk_all --check              # the roots AreaLaw.lean, AreaLawForMathlib.lean, OpenAI.lean are up to date
```

The build contains no `sorry` outside `Challenge/`. Every result, including `AreaLaw.areaLaw`,
depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

The trust boundary of a formalization is its statement layer. The paper's objects are encoded in
`OpenAI/Statements.lean`, which `docs/StatementAudit.md` compares with the paper clause by
clause. The deviations from the paper's conventions (proofs carried out over `ℂ` and transferred
to an arbitrary `RCLike` field, the real parameter `D₀`, the lattice encoding of templates and
cuts) are recorded in `docs/oai265/Memory.md` and `RefactoringResult.md` §2 and §5.

## The comparator

`Challenge/Basic.lean` restates Theorem 1.1 with every definition it needs copied in,
importing only Mathlib and Physlib, and leaves the theorem and two partial-trace facts
(`Arealaw.posSemidef_ptrace`, `Arealaw.trace_ptrace`) as `sorry`. `Solution/Basic.lean` proves
them from the development (`OpenAI.Challenge.area_law` applies `AreaLaw.areaLaw`).
`Comparator/comparator.json` fixes the theorem names and the permitted axioms;
[comparator](https://github.com/leanprover/comparator) checks that the solution proves exactly the
challenge's statements with only those axioms:

```bash
comparator Comparator/comparator.json
```

## The blueprint

`blueprint/` is a [Verso Blueprint](https://github.com/leanprover/verso-blueprint) package: one
chapter per paper section, one node per digest anchor, each linked to its Lean declaration. Its
dependency graph is checked against the digest's DAG (`blueprint/scripts/check_dag.py`).

```bash
lake build                      # the library first
cd blueprint && ./scripts/ci-pages.sh   # site in blueprint/_out/site/html-multi/
```

## Provenance

Version 1 (October 12 to 16, 2026) proved every result above in the `OpenAI/` tree. The proofs
were produced by Axiom's agent tooling and OpenAI Codex, directed by Ruiz Chen, who froze the
statement layer on October 13 and audited it, and checked each result independently. It has
been public since October 16, tag `v1.0`; its history is in `HISTORY.md`.

Version 2 (October 19 to 21, 2026) restructured the proofs into the paper's shape, directed by
Michał Mogielnicki: one module per section with the paper's numbering in `AreaLaw/`, general
results in `AreaLawForMathlib/`, the digest and the blueprint. `Map.md` records the faithfulness
of v1 against the paper's anchors.

The code of v1 that the restructuring removed stays in tag `v1.0` with its history, and the
ported code keeps its attribution: every file ported from
[LionSR/TNLean](https://github.com/LionSR/TNLean) or
[LionSR/QICLean](https://github.com/LionSR/QICLean) names its source in its header, and
`NOTICE` lists both projects.

## License

Apache License 2.0; see `LICENSE` and `NOTICE`.
