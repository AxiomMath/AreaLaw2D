# A two-dimensional area law from a global spectral gap, in Lean 4

This repository contains a Lean 4 formalization of

> OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
> family 265 of [openai/math](https://github.com/openai/math) (revision `adc7f1241b42`).

Theorem 1.1 of that paper (the area law for gapped nearest-neighbour Hamiltonians on finite
subdomains of the square lattice) and Corollary 1.2 are proved, together with every intermediate
proposition the paper exports: Proposition 4.3 (positive quasilocal replacement of the gap),
Proposition 9.6 (collar bound), Proposition 10.2 (amplification), Proposition 11.2 (two-family
decomposition), and the lemmas of Sections 2, 3 and 11.

## Where things are

| Path | Content |
| --- | --- |
| `OpenAI/Statements.lean` | The statement layer: lattice domains, admissible Hamiltonians, the global gap, the edge boundary, and the paper's results as `def ... : Prop`. Every definition is total and free of `sorry`. This file was frozen before any proof was written and has not changed since, apart from removing the proof stubs as results were proved. |
| `OpenAI/AreaLaw.lean` | `OpenAI.area_law` (Theorem 1.1) and `OpenAI.area_law_corollary` (Corollary 1.2). |
| `OpenAI/PositiveReplacement.lean`, `OpenAI/CollarBound.lean`, `OpenAI/Amplification.lean`, `OpenAI/TwoFamilyDecomposition.lean`, `OpenAI/TwoFamily.lean` | Propositions 4.3, 9.6, 10.2, 11.2 and Lemma 11.1. |
| `OpenAI/` (remaining modules) | The supporting theory: entropy and conditional entropy, Lieb-Robinson bounds, spectral filters, comparators, the scanner, the dyadic geometry of Section 11. |
| `OpenAI/Audit.lean`, `OpenAI/AuditAreaLaw.lean` | `#print axioms` for every proved result. |
| `Challenge/`, `Solution/`, `Comparator/` | The comparator pair for Theorem 1.1: `Challenge/Basic.lean` restates `OpenAI.area_law` with every definition it needs copied in, importing only Mathlib and Physlib, and leaves the objective and two partial-trace facts as `sorry` by design; `Solution/` proves them from the development; `Comparator/` records the run that accepted the solution. These three `sorry` in the challenge file are the only ones in the repository. |
| `Arealaw/` | The region, partial trace and entropy library the statement layer is built on, developed for the Brandão-Horodecki area law (arXiv:1206.2947) in the `quantum-arealaw` project. |
| `docs/oai265/` | Working notes: the plan, the inventory of what existed upstream, the record of every decision and deviation from the paper, and one plan file per proposition. |

## Verification

```bash
lake exe cache get
lake build OpenAI
lake env lean OpenAI/Audit.lean
lake env lean OpenAI/AuditAreaLaw.lean
```

The build contains no `sorry`. Every result, including `OpenAI.area_law`, depends only on the
axioms `propext`, `Classical.choice` and `Quot.sound`.

The trust boundary of a formalization is its statement layer. The paper's objects are encoded in
`OpenAI/Statements.lean` and the deviations from the paper's conventions (proofs carried out over
`ℂ` and transferred to an arbitrary `RCLike` field, the real parameter `D₀`, the lattice encoding
of templates and cuts) are recorded in `docs/oai265/Memory.md`.

## Provenance

Parts of the supporting theory are ported from two Apache 2.0 projects, with the source
repository, file and commit recorded in the header of every ported file:

* [LionSR/TNLean](https://github.com/LionSR/TNLean), the tensor-network library, whose
  independent formalization of this paper covers Sections 2 to 4 and much of the geometry of
  Section 11;
* [LionSR/QICLean](https://github.com/LionSR/QICLean), its quantum-information dependency.

The two-family decomposition (Proposition 11.2), the collar bound (Proposition 9.6), the
amplification (Proposition 10.2) and the final assembly were proved here from the paper; the
notes in `docs/oai265/` say for each file whether it is a port or native.

The proofs were produced by Axiom's agents (AxiomCode and OpenAI Codex), directed by Ruiz Chen,
who froze and audited the statement layer and checked each result independently. The history of
the development is in `HISTORY.md`.

## Dependencies

Lean `v4.33.0`, Mathlib `v4.33.0`, [Physlib](https://github.com/leanprover-community/physlib)
at the commit pinned in `lake-manifest.json`.

## License

Apache License 2.0; see `LICENSE` and `NOTICE`.
