# Three-dimensional targets for the area law

This document fixes the statements that a three-dimensional continuation of the two-dimensional area law should aim at. The statements are in `OpenAI/Statements3D.lean`; every one is a `def … : Prop` with no proof attached. The paper is [OAI265], *A two-dimensional area law from a global spectral gap* (24 September 2026, unrefereed), cited by section, equation and result number. Lean declarations are cited by name; the 2D ones are in `OpenAI/Statements.lean` unless another file is named.

Two dimension tables informed the verdicts. The first is §3 of a reader's guide to the paper and its formalization, which lists sixteen places where dimension two enters, cited here as "report item 1" to "report item 16". The second is the "Dimension" table of a refactoring map, which classifies 238 paper anchors as `any d`, `graph` or `2D only`, cited here by anchor (for example "Map D9.25"). Neither file is in this repository. Where they disagree I record the disagreement; where I add an observation of my own I say so.

## 0. Encoding

Sites are `ℤ × ℤ × ℤ` with Mathlib's graph `hasse ℤ □ (hasse ℤ □ hasse ℤ)` (`cubicLattice3D`). This is the smallest change to the 2D encoding `ℤ × ℤ` with `hasse ℤ □ hasse ℤ`. The product order gives integer boxes as `Finset.Icc`, the product extended metric is the sup norm `dist_∞` of §3.2, and pointwise addition of finsets gives the dilations `T_j` of §2.2, all with the same constructions as in 2D. The alternative `Fin 3 → ℤ` also carries the sup metric and the order, but Mathlib gives it no lattice graph, so its adjacency would be written by hand. A slab `ℤ² × [0, h)` is encoded as a set of sites of `ℤ³` with third coordinate in `[0, h)`, so slab statements and cubic statements share every definition.

Each 3D definition that generalizes a 2D one carries the suffix `3D`, and its docstring says what changed: `domainEDist3D`, `domainEDiam3D`, `graphNbhd3D`, `domainComponent3D`, `edgeBoundary3D`, `cutEndpoints3D`, `ambientEDist3D`, `ambientDilation3D`, `Qudits3D`, `supports3D`, `hamiltonian3D`, `IsAdmissible3D`, `IsTemplate3D`, `IsSeparatedFromCut3D`, `collarWidth3D`, `IsIntBox3D`, `boxSize3D`, `IsSafe3D`. The global gap `HasGlobalGap`, the pure state `pureState`, the conditional expectation `condExpect` and the entropies are reused unchanged, since they never mention the lattice. Three 2D statements already quantify over an arbitrary site type and therefore are already 3D statements: `TwoFamilyCancellation` (Lemma 11.1, proved for every site type as `two_family_cancellation` in `OpenAI/TwoFamily.lean`), `ConditionalContinuity` (Lemma 2.1) and `MarginalTails` (Lemma 3.1).

The one choice that is not forced is the shape of a 3D template piece (`IsTemplatePiece3D`). In 2D a piece is a rectangle or triangle with sides of slope `0`, `∞`, `1`, `-1` (Definition 9.3, `IsTemplatePiece`). In 3D I take every polytope with nonempty interior cut out by one pair of inequalities `lo ≤ ⟨v, x⟩ ≤ hi` for each of the 26 nonzero vectors `v ∈ {-1, 0, 1}³`. This class contains boxes, prisms over the planar pieces and the simplices of the barycentric subdivision of a cube, and every lattice row of such a piece is an interval, which is what the 2D proofs of the template bounds use (report item 6). Because the piece family that a 3D version of Section 11 would need is unknown, the class is deliberately broad. A broader class makes the collar bound harder and the geometric decomposition easier.

## A. The north star: `AreaLaw3D`

**Statement.** For fixed `q`, `R`, `J` and `Δ > 0` there is a constant `C` such that for every finite domain `Λ ⊂ ℤ³`, every Hamiltonian `H = ∑_X h_X` with Hermitian terms of norm at most `J` supported on sets of induced-graph diameter at most `R`, every normalized eigenvector `Ω` of `H` with eigenvalue `E₀` and global gap `H − E₀ ≥ Δ (1 − |Ω⟩⟨Ω|)`, and every `A ⊆ Λ`,

  S(ρ_A) ≤ C |∂_Λ A|,

where `∂_Λ A` is the set of nearest-neighbour edges of `ℤ³` between `A` and `Λ \ A`. This is Theorem 1.1 (eq. (1.2)) with `ℤ³` in place of `ℤ²`. Lean: `AreaLaw3D`, which differs from `AreaLaw` only in using the `3D` lattice notions.

**This is not a target.** The 2D proof does not reach it, for reasons that need new mathematics, not new bookkeeping. Section C lists them: the scanner exponents of §9 (C.1), the first subvolume exponent of §3.3 (C.2), the amplification radius of §10 (C.3) and the point contacts of §11 (C.4). Any document or commit that claims progress on `AreaLaw3D` should say which of the four it resolves.

## B. Partial targets

Each target below is a self-contained statement on `ℤ³`. The order is by expected difficulty.

### B.1 Cylinders over a planar domain (a corollary)

**Statement.** For a planar domain `Λ' ⊂ ℤ²` and `h ≥ 1`, let `Λ = Λ' × [0, h)`. For every admissible Hamiltonian on `Λ` with a gapped unique ground state and every cut `A ⊆ Λ`, including cuts that split columns, `S(ρ_A) ≤ C_h |∂_Λ A|`.

**Lean.** `CylinderAreaLaw3D 𝕜 q R J Δ h` (domains with `IsCylinderDomain3D h Λ`), and the reduction `CylinderAreaLawOfPlanar3D 𝕜 q R J Δ h`, which says that the planar area law `AreaLaw 𝕜 (q ^ h) R J' Δ` at every strength `J' > 0` implies `CylinderAreaLaw3D 𝕜 q R J Δ h`. Both are proved in `OpenAI/Cylinder3D.lean`: the reduction as `OpenAI.cylinderAreaLawOfPlanar3D` for every parameter set, and the cylinder law as `OpenAI.cylinderAreaLaw3D` for every `q`, `R`, `J`, `h` and every `Δ > 0`.

**Hypotheses.** Those of `AreaLaw3D`, restricted to cylinder domains. The reduction itself has no hypothesis; combined with `area_law` (`OpenAI/AreaLaw.lean`, which assumes `1 ≤ q`, `0 < J`, `0 < Δ`) it gives the cylinder law for `1 ≤ q` and `0 < Δ`.

**It is a corollary of the 2D theorem.** Group each column `{u} × [0, h)` into one planar site with local dimension `q^h`. A path in `Λ` projects to a walk in `Λ'`, so `d_{Λ'} ≤ d_Λ` and every support keeps diameter at most `R`. Terms with the same projected support add up; there are at most `2^{h(2R+1)²}` of them, so the planar strength is `J' = 2^{h(2R+1)²} J`. The spectrum and the ground state do not change. For a cut `A`, let `A*` be the union of the columns that meet `A`. Then `S(A) ≤ S(A*) + S(A* \ A) ≤ S(A*) + (h − 1) log q · m`, where `m` is the number of columns that meet both `A` and `Λ \ A` (Araki-Lieb). Since columns are full, each such column contains a vertical crossing edge, and each planar crossing edge of `A*` lifts to a horizontal crossing edge of `A` in the same layer. Hence `m + |∂_{Λ'} A*| ≤ |∂_Λ A|`, and `C_h = C_2D(q^h, R, J') + h log q` works. The constant grows with `h` through `C_2D(q^h, …)`, whose dependence on `q` the paper does not make explicit.

**Reused unchanged.** The whole 2D theorem `area_law`, as a black box. **New work.** A reindexing between `Reg (Qudits3D q) Λ` and `Reg (Qudits (q ^ h)) Λ'`, the transfer of Hamiltonian, gap and entropy along it, the Araki-Lieb step, and the edge count above. No 2D lemma needs a 3D restatement.

**Verdict.** Provable with modest work; it is worth stating as the first 3D theorem on record, and it is not more than a corollary.

**Question for a physicist.** Should the slab constant be expected to stay bounded as `h → ∞` for fixed `q`, `R`, `J`, `Δ` (which would be a statement about 3D), or is linear growth in `h`, as the column argument gives at best, the honest expectation?

### B.2 Arbitrary domains inside a slab

**Statement.** As in B.1, but `Λ` is any finite subset of `ℤ² × [0, h)` (`IsSlabDomain3D h Λ`). Lean: `SlabAreaLaw3D 𝕜 q R J Δ h`. It implies B.1.

**Why it is not a corollary.** The column argument needs full columns. A domain inside a slab can contain two sheets, say at heights `0` and `2`, joined only far away. For the cut "lower sheet", the true boundary is small, but every column over the sheets is split and has no vertical crossing edge, so the bound through `A*` is of the order of the sheet area. I see no way to repair this by padding the domain with decoupled sites, since the padded sites create crossing edges of their own.

**Route.** Rerun the 2D proof with sites fibred over `ℤ²`: ambient geometry is done on the projection to `ℤ²`, and the physical regions are the sites of `Λ` above the planar sets. Graph distance in `Λ` still dominates the projected sup distance, which is the only link between graph and ambient geometry that §§9 to 11 use (report item 9; Map D9.1, D10.16). Every perimeter or row count acquires a factor `h` and stays linear in the planar scale, so the 2D-only steps keep their 2D form: the harmonic sum of Lemma 3.2 still diverges (report item 4; Map D3.4, D3.6, D3.10), rows still have `O(h n)` sites (report item 7), and Section 11 is applied to the projected endpoint set, which has at most `2|∂_Λ A|` points (report items 10 to 16; Map D11.4).

**Reused unchanged.** Sections 2 to 8 and 10 (report items 1 to 3 and 9; Map D2 to D8, D10), the planar geometry of §§9.3 and 11 applied to projections. **New work.** Every Lean statement on `ℤ × ℤ` must be restated for a site type with a projection to `ℤ²` and fibres of size at most `h`. This is large but, as far as I can see, mechanical. I am not certain that no step of Section 11 uses the fact that a planar tile contains whole columns; I found none.

**Verdict.** Plausible with bounded new work, most of it restating; the risk is volume, not mathematics.

**Question for a physicist.** For a folded domain whose two sheets are adjacent in space but far apart along the lattice, is there any physical mechanism, under a global gap only, by which the sheets could share entanglement proportional to their common area?

### B.3 Positive replacement on `ℤ³`

**Statement.** Proposition 4.3 on `ℤ³`, for each integer `p ≥ 1` and `α = p/(p+1)`: there are `c_* > 0`, `C`, `c > 0` and operators `0 ≤ k_X ≤ 1` with `k_X Ω = 0`, `∑ k_X ≥ c_*⁻¹ (H − E₀) ≥ (Δ / c_*)(1 − |Ω⟩⟨Ω|)`, `‖k_X − E_{X,l}(k_X)‖ ≤ C e^{−c l^α}` with `E_{X,l}(k_X) ∈ [0, 1]`, and `k_X` supported in the component of its anchor. Lean: `PositiveReplacement3D 𝕜 q R J Δ p`; the target is this for every `p ≥ 1`, `1 ≤ q`, `0 < J`, `0 < Δ`.

**Reused unchanged.** The Lieb-Robinson bound `QuantumCircuit.norm_heisenberg_commutator_le_graphDistance` holds on any finite graph (`OpenAI/LiebRobinson/GraphPropagation.lean`; report item 2), the Gevrey filter of Lemma 4.2 has no geometry (Map D4.5), and the square-root step (eq. (4.13)) is operator theory (Map D4.9, D4.10). **Replaced.** The counting constants: sites per support `(2R+1)³` in place of `(2R+1)²` (`card_le_of_mem_supports`, `OpenAI/SupportCounting.lean`), graph balls of size `O(l³)` in place of `O(l²)` (`card_graphBall_domainGraph_le`, `OpenAI/LatticeCounts.lean`; report item 1; Map D2.7 to D2.9, D4.3, D4.4). Only polynomial ball growth is used against stretched exponential tails.

**Verdict.** Provable with bounded new work; it is the most routine of the targets and the foundation of B.4.

**Question for a physicist.** The construction replaces each filtered term `M_X` by `|M_X|`, losing a square root in the locality tail; is there a known reason in three dimensions to expect a worse tail for `|M_X|` than the square root of the tail of `M_X`?

### B.4 Amplification on `ℤ³`

**Statement.** Proposition 10.2 on `ℤ³` with a collar exponent `θ > 1`. Fix `C₀ > 0` and `M ≥ 1`. For a set `T`, a collar width `L`, `X = A ∩ T` and `S₀ = A ∩ T_L`, assume `|S₀| ≤ C₀ n³`, that the cuts `X`, `S₀ \ X`, `S₀` have at most `C₀ n²` edges, and `I_Ω(X : Λ \ S₀) ≤ C₀ n^θ`. Then at all large `n` there is a radius `r ≤ C_M n^{θ/α}` with `I_Ω(X' : J) ≤ C_M n^{−M}` for every `X' ⊆ X` and every `J ⊆ Λ \ N_{2r}(S₀)`; and `N_{2r}(S₀) ⊆ A` whenever `dist_∞(T, Z_A) > L + 2r`. Lean: `Amplification3D 𝕜 q R J Δ p θ`; the target is this for every `p ≥ 1` and `θ > 1`.

**Why `θ > 1` and `n^{θ/α}`.** These are forced by the paper's own bookkeeping, not chosen. The proof sets a spectral window `w` (eq. (10.19), `w = n^{3/5}` in 2D) and needs the Lemma 3.1 tail `exp(−w / (32 √((1+ϑ)B)))` to be below `n^{−2K}`, where `B` grows like the number of crossing terms. In 3D that number is `O(n²)`, so `√B ≍ n` and any `w = n^θ` with `θ > 1` works. The clock time is `t_* = C(I + w + K log n)` and the radius is `r = ⌈(C′(t_* + K log n))^{1/α}⌉` (eq. (10.29)), so `I ≤ C₀ n^θ` gives `r ≤ C_M n^{θ/α}`. The final continuity step costs `log dim e′ = |X| log q ≤ C n³` in place of `C n²`, which a larger `K` absorbs. Hypotheses `I ≤ C₀ n^{θ′}` with `θ′ ≤ 1` are covered by taking `θ` slightly above 1.

**Reused unchanged.** Report item 9 and Map D10.1 to D10.17 classify every step as `any d` or `graph`; Lemma 10.1 (the dissipative Lieb-Robinson bound) needs polynomial ball growth only (Map D10.2), and the cut clearance uses only that one lattice step changes sup distance by at most one (`graphNeighborhood_subset_of_cut_clearance`, `OpenAI/GraphNeighborhoodCutClearance.lean`). The 2D Lean proof is `amplification` (`OpenAI/Amplification.lean`). **Replaced.** The window `w`, the choice of `K`, and the clearance clause, which names `L + 2r` instead of the 2D threshold `L + n^β`. The collar width `L` is a free parameter because no clause depends on its value.

**Verdict.** Provable with bounded new work. Its use is another matter: in 3D the radius `r` exceeds `n`, which is open problem C.3.

**Question for a physicist.** For a gapped ground state, is the spectrum of `−log ρ_X` known to concentrate in a window narrower than the square root of the number of terms crossing the boundary of `X`? A window of size `|∂X|^{1/2 − δ}` would remove the window's contribution to a radius above `n`; the contribution of the collar information `I` would remain.

### B.5 The assembly

**Statement.** If, for some `0 < ε < 1/2`, some `p ≥ 1` and some `β > (2 − 2ε)(p + 1)/p`, the 3D collar bound with exponent `ε`, 3D amplification with `θ = 2 − 2ε`, and the 3D two-family decomposition with exponents `ε`, `β` all hold, then `AreaLaw3D` holds (for `1 ≤ q`, `0 < J`, `0 < Δ`). Lean: `AreaLawAssembly3D 𝕜 q R J Δ`, which takes `CollarBound3D`, `Amplification3D` and `TwoFamilyDecomposition3D` as hypotheses.

**Why these exponents.** The collar bound gives `I ≤ C (n²)^{1−ε} = C n^{2−2ε}`; amplification then gives `r ≤ C_M n^{(2−2ε)/α}`; §11.8 needs `L + 2r < 2 n^β` at large `n` to place `J_i = (Λ \ A) ∪ (earlier tiles of the same family)` outside `N_{2r}(S_i)`, using (11.3) and (11.4). With `L = ⌊n^{1−ε}⌋` this holds at large `n` when `β > (2−2ε)/α`.

**Reused unchanged.** The structure of `area_law` and `exists_mutualInfo_exterior_union_le` (`OpenAI/AreaLaw.lean`; report §2.5), `two_family_cancellation`, which is already proved for every site type (Map D11.1), and the path argument (Map D10.16, D11.26). **Replaced.** Lemma 2.2 (`regionEntropy_eq_zero_of_edgeBoundary_eq_empty`, `OpenAI/ZeroBoundary.lean`) and the volume bound `regionEntropy_le_card_mul_log` (`OpenAI/BoxEntropy.lean`) must be restated on `ℤ³`; both are graph arguments.

**Verdict.** Provable with bounded new work; it does not advance `AreaLaw3D` by itself, but it freezes the interface: once the three inputs exist, nothing else is needed. Its hypotheses are not known to be consistent; in particular `β > 1` is required, which no planar-style decomposition provides (C.3, C.4).

**Question for a physicist.** Lemma 11.1 needs exactly two families and tiles of one family that are nearly independent of the earlier ones. Is there a known entropy inequality of this kind that tolerates tiles of the same family touching along a curve, at a cost proportional to the length of the contact?

### Candidates evaluated and not kept

*Regions with simple boundary* (boxes, unions of boxes, or cuts whose boundary avoids the contact problem). Restricting the shape of `A` does not isolate Section 11. The contacts of §11.4 arise between tiles inside `A`, not on its boundary: even for a cube, the layers at distance `2^k` from the cut must be cut into tiles of comparable size, and in space two families of tiles necessarily touch along edges (C.4). The analytic gaps C.1 to C.3 also apply to every template inside `A`, whatever its shape. Cuts of bounded thickness (every site of `A` within distance `w` of the cut) satisfy `|A| ≤ C w |∂_Λ A|`, so the area law for them follows from `S(A) ≤ |A| log q` and is trivial. I found no class between these two extremes that avoids both the analytic and the geometric gaps, and I did not keep the candidate.

*The analytic core as one target.* The candidate "Propositions 9.6 and 10.2 on `ℤ³` with row size `n²`" splits. Proposition 10.2 survives as B.4. Proposition 9.6 is the open analytic problem and is frozen as `CollarBound3D` in C.1, not as a target with a plausibility claim.

## C. Open problems

Each item is written for a reader who knows the physics but not the Lean. The frozen statements are listed so that later work has a fixed interface; none of them is a target.

### C.1 The scanner exponent bookkeeping

Proposition 9.6 bounds the mutual information between a template `X = A ∩ T` of linear scale `n` and everything beyond a collar of width `L = n^{1−ε}`: `I(X : Λ \ S₀) ≤ C n^{1−ε}` with `ε = 10⁻⁵`. The proof runs `k` replicas, slides partitions across the collar along a random schedule (the scanner, §9.1 and Lemma 9.1) and compares two norm estimates (Proposition 8.1); the error terms are tabulated after (9.20), with exponents such as `0.999952` against the target `1 − ε = 0.99999`. In 2D a depth row around a template has about `n` sites and the scanner pads each row to `n` slots (eq. (9.2), (9.3)). In 3D a row is a surface of about `n²` sites, and the frozen 3D statement asks for `I ≤ C (n²)^{1−ε}` for some `ε ∈ (0, 1)`, with cuts `O(n²)` and `|S₀| = O(n³)`. Lean: `CollarBound3D 𝕜 q R J Δ ε`.

**The two tables disagree here, and I do not resolve it.** The report (item 7) says the scanner logic does not use planarity but that whether the error terms, polynomial in `n²` per row, still fit under `n^{2−ε}` "is a computation that neither the paper nor the formalization does": unclear. The Map classifies all of §9.1 to §9.5 except the template geometry as `any d` with re-tuned exponents (D1.16, D9.2, D9.9, D9.25, D9.26, D9.29: "thin margin 0.999952 vs 0.99999 must be re-tuned for row size `n^{d−1}`"). The Map measures scale by row size (D9.3 writes `|T| ≤ C n^{d/(d−1)}`); `CollarBound3D` measures it by linear size, so the Map's `n` is this file's `n²`.

What the constraints become. In (9.1) the parameters `L = n^{1−ℓ}`, `m = n^μ`, `D = n^κ` with `0 < κ < μ < 1 − ℓ` are lengths and need not change. In (9.2) the hypotheses `|T| ≤ C n²` and `|T_j \ T_{j−1}| ≤ n` become `C n³` and `C n²`. The charge lottery picks among `O(nD)` anchors (§9.1); in 3D among `O(n²D)`, so the per-round charging probability `c/(nD)` becomes `c/(n²D)` and the number of rounds `nm` becomes `n²m`. The window `w` of the typical projections must exceed `√(n²) = n` (compare B.4). Whether every row of the table after (9.20) then stays below `2(1−ε)` for one positive `ε` is the question. In (11.2) and (11.16) the same exponent `ℓ` reappears as `(1 + 2δ₀)(1 − ℓ) < 1` and `L = o(r)`, next to the clearance exponent `β`, which C.3 shows cannot keep its planar role.

### C.2 The first subvolume exponent

The bootstrap of Proposition 9.5 starts from Proposition 3.3: for safe boxes of size `r`, `S(A ∩ Q) ≤ C r^{1 + e₀}` with `e₀ < 1`, strictly below the area `r²` of a planar box. The 3D analogue, frozen as `InitialBoxEstimate3D` (exponent `2 + e₀`, `0 < e₀ < 1`), is open. Its 2D proof rests on Lemma 3.2, which applies filters on `m ≍ C_pad r / D` nested boxes with weights `a_j` of total mass two. The energy cost is `E = ∑ (crossing terms of box j) a_j²`, and the argument needs `C E / Δ ≤ 1/4` so that the filtered vector keeps overlap with `Ω` (after (3.16)). In 2D the crossing count grows like `r + d_j`, Cauchy-Schwarz gives `E = 4 / Z_r` with `Z_r = ∑ 1/(r + d_j)`, and the harmonic sum makes `E` small by a choice of `C_pad` (eq. (3.12)). In 3D the count grows like `(r + d_j)²`, the sum `∑ (r + d_j)^{−2}` is of order `1/(D r)`, and `E` grows like `D r`.

The Map (D3.4, D3.6, D3.10) calls this `2D only`. The report (items 4 and 5) calls it unclear and suggests restating the error as `C r²`. My own reading of (3.16) and (3.17) is that the obstruction is not only the size of the error: the method needs `E` small, and in 3D it is large. If a 3D Lemma 3.2 with error `C r²` were available, the colouring argument of §3.3 with `M³` children would give `F_box(M r) ≤ λ F_box(r) + C M³ r²` with `M² < λ = (1 − p₀/4) M³ < M³`, hence the exponent `2 + e₀` with `e₀ < 1`; this last step I have checked only on paper.

### C.3 The amplification radius exceeds the template (my own observation)

Both tables classify Proposition 10.2 as dimension independent (report item 9; Map D10.4, D10.11), and as a statement it is (B.4). Its use in §11.8 is not. The radius `r` must satisfy `L + 2r < 2 n^β` with `β < 1` (eq. (10.16), (11.3), (11.4)) so that the decoupled region stays inside the template's own layer. In 3D the construction behind B.4 uses a radius of order at least `n^{θ/α}` with `θ > 1`, so `r > n`, from the spectral window alone and whatever the collar bound: the window must exceed the square root of the number of crossing terms, which for a template of linear size `n` is of order `n`. With the collar bound of C.1 the radius is about `n^{2(1−ε)/α}`, close to `n²`. So in 3D the decoupled region is larger than the template by a power, and the assembly needs a clearance exponent `β > 1` (B.5).

This conflicts with the planar constraints. For a primary tile in layer `k` (cell size `r_k = 2^k`) the 2D proof takes `n ≍ r_k^{1 + 2δ₀}` (eq. (11.15)) and needs `n^β = o(r_k)` and `n^β = o(t_k)` (eq. (11.16)), that is `(1 + 2δ₀) β < ζ < 1` (eq. (11.2)). In 3D the count of pieces gives `n ≍ r_k^{1 + 3δ₀}`, and the belt count `C b r³ / (s_k t_k²)` decays only if `ζ > 1 − δ₀/2` (report item 11; Map D11.9: the paper's `ζ = 1 − δ₀/2` gives no decay). Together they can be met with `β < 1`. With `β > 1` the first fails: a primary is at least as large as a layer cell, so `n^β ≥ r_k^β`, which is not `o(r_k)`; the tile would have to lie farther from the cut than its own layer. Either the amplification radius must be brought below `n` (a sharper window than Lemma 3.1, or a different decoupling mechanism), or the geometry must use tiles much smaller than their separation from the cut and from earlier tiles of their family. I have not seen either addressed. I am fairly confident in the arithmetic and less confident that no reorganization of §10 avoids it.

### C.4 The point contact problem

In 2D, Section 11 covers all of `A` except `O(|∂A|)` sites by tiles in two families, so that tiles of one family stay at distance `2n^β` from the cut and from the earlier tiles of their family. Strips ("belts") separate the tiles of a layer, and a fan of at most eight triangles in each belt cell makes tiles of the same family touch only at isolated points (§11.4). Each point contact is then removed by cutting a small square around it and relabelling its eight sectors; this produces new point contacts at a smaller scale, and the recursion stops after `O(log log)` generations with a polylogarithmic number of descendants (§11.5, Lemmas 11.3 to 11.5, eq. (11.12)). Both tables agree that this is planar (report items 12 to 14; Map D11.11 to D11.15, D11.18, D11.19, D11.22).

In space the contacts cannot be made pointlike. Around an edge of a polyhedral partition sit at least three cells in cyclic order, each sharing a face with the next. If the cells carry two labels and no two cells with the same label share a face, the labels alternate, so the number is even and at least four, and the first and third cells share the label and the whole edge. Contacts of codimension two, that is curves, are therefore unavoidable, as the report's example of four cubes around an edge shows (item 12). Removing a tube around a contact curve and relabelling it creates long thin tiles, whose template scale is their length and whose required separation `n^β` then exceeds their width; cutting the tube into short pieces creates new contacts along the curve. The frozen statement is `TwoFamilyDecomposition3D ε β`, Proposition 11.2 on `ℤ³` with the exponents as parameters, and the assembly needs it with `β > 1` (C.3), which makes it harder still. An entropy cancellation that tolerated contacts along curves at a cost proportional to their length would not suffice by itself: a layer can contain `O(|∂A|)` cells (eq. (11.5)), so such costs sum over layers only with an extra decay in the layer index, which in 2D the sparse belts provide (eq. (11.7), (11.13)).

## D. How to use this document

1. Every 3D proof attempt in this repository targets one of the frozen statements in `OpenAI/Statements3D.lean`: `CylinderAreaLawOfPlanar3D`, `SlabAreaLaw3D`, `PositiveReplacement3D`, `Amplification3D`, `AreaLawAssembly3D`, or one of the open statements `CollarBound3D`, `InitialBoxEstimate3D`, `TwoFamilyDecomposition3D`, or the north star `AreaLaw3D`. A proof is a `theorem` in a new file whose type is the frozen `def` applied to its parameters, with the hypotheses listed in this document and nothing more.
2. The statements do not change once proofs start. If a statement turns out to be false or unprovable as frozen, the fix is a new statement with a new name next to the old one, and a note in this document saying why; the old one stays.
3. A result on a weaker or differently shaped statement is recorded as such, not as progress on the frozen one.
4. Claims about the paper cite a section, equation or result number; claims about the Lean cite a declaration.

## Uncertainties

- The verdicts in B rest on the two tables and on my reading of the paper; no 3D proof has been attempted.
- B.2 assumes no step of Section 11 uses that a planar tile contains whole columns.
- C.2 and C.3 are my own readings of (3.16), (10.19), (10.29), (11.2) and (11.16). They go beyond both tables, which classify Proposition 10.2 as dimension independent.
- The template piece class of `IsTemplatePiece3D` is a choice; a 3D Section 11 might need other pieces, in which case `CollarBound3D` and `TwoFamilyDecomposition3D` would have to be restated under new names.
