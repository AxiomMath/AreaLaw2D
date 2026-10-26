# Working charter for `quantum-arealaw`

## What this repo is

Two layers on Lean 4 + Mathlib + physlib: a **worked example** (the dimer / EPR-pair area law,
Brandão–Horodecki arXiv:1309.3789, Fig. 1a + Eq. 3), and a **library layer** for the
mathematics the full paper (arXiv:1206.2947) is stated in: mixed states on a chain, regions
as `Finset`s, the partial trace between nested regions, purification, entropies.

Scope is what the area law needs, but the library layer must be reusable, not scaffolding for
one theorem. Write the *reference-quality* version of the slice it covers, not the *quickest*.

## Acceptance criteria (the owner set these)

Done means all three:

1. **Zero `sorry` + auditable axioms.** No `sorry`, no `native_decide`, no custom `axiom`.
   Every headline result is enrolled in `Audit.lean` and shows only
   `{propext, Classical.choice, Quot.sound}`. CI gates the enrolled declarations only and the
   build merely warns on `sorry`, so enrolling is part of the work. Never merge below this.

2. **Definitions orthogonal.** An assumption only a consumer needs (normalization, a fixed
   dimension, a particular index type) belongs in the *consuming theorem's hypotheses*, never
   the definition. Each basic fact gets a named, reusable lemma; the test is stateability, so a
   `have` mentioning nothing local to its proof is a lemma, lifted and named.

3. **Generality over the field: `RCLike 𝕜`, not just `ℂ`.** Everything that is not a named
   concrete instance is stated over a general `RCLike 𝕜`. Hardcode `ℂ` only where a pinned
   upstream forces it: a missing Mathlib generality, or a physlib declaration itself `ℂ`-only.

**Name every deviation in place.** A hardcoded `ℂ`, a wrapper, a universe pin, a divergence
from the paper: say so where it happens and why.

## Hard constraints

- **Remote: `AxiomMath/quantum-arealaw` (internal).** Push only there; publishing is the
  owner's decision.
- Dependencies and versions are whatever the lakefile pins. Do not reintroduce the
  "Mathlib-only, never add a QI library" rule; owner decision reversed it (2026-08). Before
  writing a definition, check the pinned upstreams and either use one or say why we own it.

## Conventions

**Process.** Build incrementally; before declaring anything done, run a clean build
(`rm -rf .lake/build/lib/lean/Arealaw .lake/build/ir/Arealaw && lake build`) plus the axiom
audit. Develop tricky proofs in a gitignored `Arealaw/Probe.lean` and never commit it.

**Files and names.** The README carries the layout, the build, and the axiom audit; follow
the file you are editing for anything it and the rules below leave open.

- Never `import Mathlib`. Prefer `open scoped X`; the exception is a namespace whose notation
  dominates a file (`open Matrix` in the matrix modules).
- **Names key to what the declaration returns:** `Prop` → `snake_case`; data →
  `lowerCamelCase`; a `Type` or family of types → `UpperCamelCase`. Hypotheses appear in order
  (`..._eq_of_...`). *Exception:* a quantity with established one- or two-character notation in
  the literature keeps it verbatim (`EE`, `H`, `H₂`, and `D₁`, `Cor` when they land), since `ee`
  is unreadable and bare `h` collides with the hypothesis convention. No underscore in a `def`
  name: Mathlib's naming linter rejects it, so a min-entropy is `minEntropy`, not `H_min`.
- **Every definition and major theorem has a doc string.**  It conveys the mathematical
  meaning of the declaration, and is allowed to lie slightly about the actual implementation.
  Omit one only where it could say nothing the statement does not.  A complete sentence ends
  in a period; a named theorem is bold faced (`**Araki–Lieb**`).  Where a hypothesis is
  necessary, say why, with a counterexample where short.
- **A module docstring is a first-level title followed by a summary of the file.**  The other
  sections, second-level and in this order, are `## Main definitions`, `## Main statements`,
  `## Notation`, `## Implementation notes`.  Use them only where the file is long enough to
  need a map, and list the load-bearing declarations rather than every one; a short file's
  summary covers them.  Rationale goes in `## Implementation notes`, never a declaration
  docstring.
- **No LLM prose.**  Cut filler openers (`Note that`, `Importantly`), marketing adjectives
  (`powerful`, `robust`), trailing justification (`This is useful for...`), hedged leftovers
  (`for now`), and any sentence restating the signature.  A comment explains *why*, never
  *what*.  No bold pseudo-headings (`**Scope.**`).  No em dashes; en dashes stay in name pairs.

**API shape.**

- **Definitions are total; side conditions live on the consuming theorems.** Not even a
  hypothesis the body ignores, added to prevent misuse. The one exception is a hypothesis
  without which the definition would be *meaningless* rather than merely more general: take it,
  and supply the transport lemma callers need to move between proofs of it.
- **Every bundled map ships enough application lemmas that no downstream proof unfolds its
  structure definition:** one per direction, one per component where a domain or codomain is a
  product. Write them by hand where `@[simps]` would state them at the wrong granularity: it
  projects componentwise, wrong whenever the domain is a function type and consumers work with
  whole elements. Where an element index is unavoidable, take its side condition as an
  argument, so callers never reconstruct a proof term.
- **State lemmas as equations of the object, not of its components.** The whole-object form
  rewrites and composes; do the `ext` once, inside the lemma.
- **`@[simp]` follows from the rewrite direction, filtered by shape.** Whole-object form and no
  hypothesis `simp` cannot discharge are necessary but not sufficient: mark it only when the
  right-hand side is the normal form you want everywhere. A structural collapse qualifies; an
  unfolding or a change of representation does not. Check it does not denormalise an existing
  simp lemma's right-hand side.
- **Do not put instances in a shared `variable` block that most declarations then `omit`:**
  scope them to a section, and prefer one section-scoped `omit` to a run of `omit … in`.
- **Wrap a Mathlib definition under a domain name only when the wrapper changes behaviour:**
  reducibility, `simp`-set membership, instance resolution, which lemmas fire. A wrapper that
  only renames, or that has one caller, is an alias: inline it.
- **One spelling per operation:** where Mathlib provides notation and its scope is open, use
  it, never the qualified name: `ᴴ`, not `.conjTranspose`.

## Extending the layer

The foundational representations are settled: read them off the code and extend them. Never
introduce a parallel encoding of something already represented, or change one without
rewriting what sits on it.

- **The weaker notion is the primitive; the stronger one refines it.** Where a definition
  admits a general and a normalized form, define the general one and get the other by adding
  a field (`SubState` and `MState`), so the theory is not built twice.
- **Derived conventions are wrappers, never second primitives.** A quantity has one
  definition and its variants are defined from it: entropies are in nats, with base-2 forms
  derived over the natural-log primitive.

Status lives in the repo, not here: read `Audit.lean` and the module docstrings.
