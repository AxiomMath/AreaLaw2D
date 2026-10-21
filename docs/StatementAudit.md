# Statement audit

A clause by clause comparison of `OpenAI/Statements.lean` (the frozen statement layer) with the
LaTeX source of the paper at `openai/math@adc7f1241b42` (`build/sections/*.tex`). Read on
2026-10-16 against the final statement file, which differs from the file frozen on 2026-10-13
only by the removal of the five proof stubs (every definition is byte identical).

Conventions shared by all statements:

| Paper | Lean | Note |
| --- | --- | --- |
| Finite `Λ ⊂ ℤ²` with the induced square-lattice graph, edges at Euclidean distance one | any `Finset (ℤ × ℤ)`, graph `hasse ℤ □ hasse ℤ` induced on `Λ` | identical |
| `d_Λ` graph distance, `+∞` between components | `domainEDist : ℕ∞`, `⊤` across components and outside `Λ` | identical |
| `ℂ^q` at every site, `q ≥ 1` | `Qudits q = fun _ => Fin q`, hypothesis `1 ≤ q` | identical |
| `H = Σ_{∅ ≠ X ⊆ Λ, diam X ≤ R} h_X`, `h_X = h_X^*`, `‖h_X‖ ≤ J` (operator norm), one summand per support, possibly zero | `hamiltonian Λ Φ = Σ_{X ⊆ Λ} extendId (Φ X)` with `IsAdmissible`: every `Φ X` Hermitian, `‖Φ X‖ ≤ J` in the L2 operator norm (`Matrix.Norms.L2Operator` is open), and `Φ X = 0` unless `X` is nonempty with `d_Λ`-diameter at most `R` | identical |
| Gap `H - E₀ ≥ Δ(1 - |Ω⟩⟨Ω|)` | `HasGlobalGap`: `Δ • (1 - vecMulVec Ω (star Ω)) ≤ H - E₀ • 1` in the Loewner order (`MatrixOrder` is open) | identical |
| `S_Ω(A)` von Neumann entropy of the reduced state on `A`, natural logarithm | `(pureState Ω hΩ).regionEntropy hA = vonNeumann` of the partial trace onto `A`; `Arealaw.H` uses `Real.log`, the base 2 variants are separate definitions | identical |
| `I_Ω(X : Y)` for disjoint `X`, `Y` | `mutualInfo = S(X) + S(Y) - S(X ∪ Y)`; every use below has disjoint arguments | identical |
| `|∂_Λ A|` number of crossing edges | `(edgeBoundary Λ A).card`, `interedges A (Λ \ A)` of the lattice graph: each crossing edge once, oriented out of `A` | identical |
| `Z_A` endpoints of crossing edges | `cutEndpoints` | identical |
| `dist_∞` between finite sets, infinite for the empty set | `ambientEDist`, `Metric.infEDist` in the product (sup) metric of `ℤ × ℤ`, `⊤` for the empty set | identical |
| ambient dilation `T_j = T + ([-j, j]² ∩ ℤ²)` | `ambientDilation T j` | identical |
| graph neighbourhood `N_r(S)` | `graphNbhd Λ S r` | identical |
| Field | statements over any `RCLike 𝕜`; at `𝕜 = ℂ` the paper's setting | deliberate generalisation, strictly stronger |

## Theorem 1.1 (`AreaLaw`, `area_law`)

| Paper (`thm:area`, eq. (1.2)) | Lean | Verdict |
| --- | --- | --- |
| `C = C(q, R, J, Δ)`, one constant for all domains, Hamiltonians and sets | `∃ C, ∀ Λ Φ Ω E₀ A, …`: `C` is chosen before everything else | identical |
| `q ≥ 1`, `R ≥ 0`, `J > 0`, `Δ > 0` | `1 ≤ q`, `R : ℕ`, `0 < J`, `0 < Δ` | identical |
| unique normalized ground vector `Ω` (up to phase) with energy `E₀` | unit vector `Ω` with `H Ω = E₀ Ω` and the gap | uniqueness is not assumed; it follows from the gap with `Δ > 0`. Lean assumes less, so the theorem is at least as strong |
| `S_Ω(A) ≤ C |∂_Λ A|` for every `A ⊆ Λ` | `regionEntropy ≤ C * card (edgeBoundary Λ A)` | identical |

`C` is not required to be nonnegative; a negative `C` would only make the statement stronger.
The case `∂_Λ A = ∅` (Lemma 2.2) is part of the statement and is proved, not excluded.

## Corollary 1.2 (`AreaLawCorollary`, `area_law_corollary`)

| Paper (`cor:rectangles`) | Lean | Verdict |
| --- | --- | --- |
| nearest-neighbour interactions on every subset of a finite rectangle | `AreaLaw 𝕜 q 1 J Δ`: range `R = 1` on every finite domain | at least as strong (rectangles are domains) |
| `S ≤ 4C |∂_in A|`, `S ≤ 2C |Z_A|` with the same `C` | `VertexAreaLaw`: one `C` with the edge, inner vertex and endpoint bounds, for every `R` | identical |

## Proposition 4.3 (`PositiveReplacement`, `positive_replacement`)

| Paper (`prop:positive`, eqs. (4.8), (4.9)) | Lean | Verdict |
| --- | --- | --- |
| integer `p ≥ 1`, `α = p/(p+1)` | parameter `p` with `1 ≤ p`, exponent `p/(p+1)` | identical |
| constants `c_* > 0`, `C`, `c` depending only on `q, R, J, Δ, p` | `∃ cstar > 0, ∃ C c, 0 < c` before `Λ` | identical |
| operators `k_i` indexed by the supports with anchors `a_i ∈ X_i` | `k : Finset (ℤ × ℤ) → Matrix`, for every anchor assignment with `anchor X ∈ X` | Lean quantifies over all anchor choices, at least as strong |
| `0 ≤ k_i ≤ I`, `k_i Ω = 0` | same, for `X ∈ supports Λ R` | identical |
| `H_F = Σ k_i ≥ c_*⁻¹ (H - E₀) ≥ (Δ/c_*)(I - P_Ω)` | the two Loewner inequalities | identical |
| `k_{i,l} = E_{i,l}(k_i) ∈ [0, I]`, `‖k_i - k_{i,l}‖ ≤ C e^{-c l^α}` for `l ≥ 0` | `condExpect` onto `N_l(a_i)` (eq. (4.1): partial trace divided by `q^{|Λ \ N_l|}`, extended by the identity), bounds `0 ≤ · ≤ 1` and the tail bound for all `l : ℕ` | identical |
| each `k_i` supported in the component of `a_i` | `IsSupportedOn (domainComponent Λ (anchor X))` | identical |

## Definition 9.3 (`IsTemplate`, `IsSeparatedFromCut`)

| Paper (`scanner:template`) | Lean | Verdict |
| --- | --- | --- |
| `s₀ ≥ 1`, `n` positive, `T` nonempty | `1 ≤ n`, `1 ≤ s₀`, `T.Nonempty` | identical |
| `T = ⋃_{a=1}^{N₀} (P_a ∩ ℤ²)`, `N₀ ≥ 1` | union of the lattice preimages of `P : Fin N₀ → Set (ℝ × ℝ)`, `1 ≤ N₀` | identical |
| each `P_a` a closed convex rectangle or triangle, sides of slope `0, ∞, 1, -1`, sup-norm diameter `≤ s₀` | `IsTemplatePiece`: hull of `a, a+u, a+u+v, a+v` with `u ⊥ v` nonzero of template slopes, or a nondegenerate triangle with template slopes; `Metric.ediam ≤ s₀` in the sup metric | identical, with rectangle and triangle read in the ordinary (nondegenerate) sense, the same convention TNLean records |
| `n ≥ C_tpl N₀ (s₀ + 1)`, `diam_∞ T ≤ n` | same | identical |
| separated from the cut: `dist_∞(T, Z) > 4 D₀ s₀` | `ofReal (4 D₀ s₀) < ambientEDist T (cutEndpoints Λ A)` | identical |

## Proposition 9.6 (`CollarBound`, `collar_bound`)

| Paper (`prop:collar`) | Lean | Verdict |
| --- | --- | --- |
| `D₀` the constant of §3.2 (any `D₀ > 2R + 10`), `C_tpl` large enough | `∀ D₀ > 2R + 10, ∃ Ctpl₀, ∀ Ctpl ≥ Ctpl₀` | the paper's "fixed, sufficiently large" constants, made explicit |
| `C` and threshold independent of `T, s₀, n, Λ, A` | `∃ C n₀` before `Λ`, `A`, `T`, `n`, `s₀` | identical |
| `L = ⌊n^{1-10⁻⁵}⌋ ≤ s₀`, `X = A ∩ T`, `S₀ = A ∩ T_L` | `collarWidth n ≤ s₀`, `A ∩ T`, `A ∩ ambientDilation T (collarWidth n)` | identical |
| for all sufficiently large `n`: `I_Ω(X : Λ \ S₀) ≤ C n^{1-ε}`, `ε = 10⁻⁵` | `n₀ ≤ n → mutualInfo ≤ C * n^(1 - 1/100000)` | identical |
| cuts of `X`, `S₀`, `S₀ \ X` have `O(n)` edges, `|S₀| = O(n²)` | the three edge counts `≤ C n`, `card S₀ ≤ C n²`, with the same `C` | identical (one constant for all five bounds is at least as strong) |

## Proposition 10.2 (`Amplification`, `amplification`)

| Paper (`prop:amplification`, eqs. (10.1), (10.15) to (10.18)) | Lean | Verdict |
| --- | --- | --- |
| `ε = 10⁻⁵`, `β = 1 - 2·10⁻⁶`, `α = p/(p+1) > 1 - 10⁻⁶` | the same numerals; the theorem takes `1 - 1/1000000 < p/(p+1)` | identical |
| fix `C₀ > 0`; for every integer `M ≥ 1`, constants `C_M` and a threshold depending on `C₀, M` only | `∀ C₀ > 0, ∀ M ≥ 1, ∃ C_M n₀` before `Λ, A, T` | identical |
| `n ≥ 2`, `L`, `X`, `S₀`, `Y = S₀ \ X`, `Z' = Λ \ S₀` | `2 ≤ n`, `collarWidth`, `A ∩ T`, `A ∩ T_L`, set differences | identical |
| hypotheses `|S₀| ≤ C₀ n²`, the cuts of `X`, `Y`, `S₀` have `≤ C₀ n` edges, `I_Ω(X : Z') ≤ C₀ n^{1-ε}` | the same five hypotheses | identical |
| conclusion: an integer radius `r ≤ C_M n^{(1-ε)/α}` | `∃ r : ℕ, r ≤ C_M * n^((1-ε)/α)` | identical |
| `L + 2r = o(n^β)` | not stated | omitted deliberately: it follows from the previous line, since `(1-ε)/α < β` when `α > 1 - 10⁻⁶` (`(1 - 10⁻⁵)/(1 - 10⁻⁶) < 1 - 2·10⁻⁶`) and `1 - ε < β`; the assembly of Theorem 1.1 uses the explicit radius bound instead |
| `I_Ω(X : J) ≤ C_M n^{-M}` for every physical `J ⊆ Λ \ N_{2r}(S₀)`, and for every subset of `X` | `∀ X' ⊆ A ∩ T, ∀ J ⊆ Λ \ graphNbhd Λ S₀ (2r), mutualInfo ≤ C_M / n^M` | identical |
| if `dist_∞(T, Z) > L + n^β` then `N_{2r}(S₀) ⊆ A` | `ofReal (collarWidth n + n^β) < ambientEDist T Z → graphNbhd Λ S₀ (2r) ⊆ A` | identical |

## Lemma 11.1 (`TwoFamilyCancellation`, `two_family_cancellation`)

| Paper (`geometry:cancellation`) | Lean | Verdict |
| --- | --- | --- |
| pure state `ψ` on a finite tensor product with site set `Λ` | any site type `σ`, local spaces `loc`, unit vector `ψ` | identical (and more general than the lattice) |
| `A = D ⊔ ⋃_{I₀} X_i ⊔ ⋃_{I₁} X_i ⊆ Λ`, each family ordered | `A = D ∪ ⋃ X_i`, `D` disjoint from each `X_i`, `X` pairwise disjoint, labels `f : Fin m → Fin 2`, the order of `Fin m` within each fibre | identical |
| `I_ψ(X_i : B ∪ ⋃_{j ∈ I_f, j < i} X_j) ≤ ε_i` with `B = Λ \ A` | the same, with the filter `f j = f i ∧ j < i` | identical |
| `S_ψ(A) ≤ S_ψ(D) + ½ Σ ε_i` | same | identical |

## Proposition 11.2 (`TwoFamilyDecomposition`, `two_family_decomposition`)

| Paper (`prop:two-families`, eqs. (11.1), (11.3), (11.4)) | Lean | Verdict |
| --- | --- | --- |
| fix `D₀`, `C_tpl` of Definition 9.3 and `n_* ≥ 1`; `C` may depend on them | `∀ D₀ Ctpl nStar, 1 ≤ nStar → ∃ C` | identical; Lean allows any real `D₀`, `Ctpl`, at least as strong |
| `Λ` finite induced subgraph, `A ⊆ Λ`, `b = |∂_Λ A| > 0` | same | identical |
| `D ⊆ A`, finite ordered family of disjoint nonempty `X_i ⊆ A`, labels, templates `T_i`, integers `n_i ≥ n_*` | `D`, `X : Fin m → …`, `f`, `T`, `n`, `s` | identical (`D ⊆ A` follows from item 1) |
| (1) `A = D ⊔ ⋃ X_i`, `|D| ≤ C b` | same | identical |
| (2) `X_i ⊆ A ∩ T_i`, `T_i` a template with parameters `(n_i, s_i)`, separated from the cut, `L_i = ⌊n_i^{1-ℓ}⌋ ≤ s_i` with `ℓ = 10⁻⁵` | `IsTemplate Ctpl (n i) (s i) (T i)`, `IsSeparatedFromCut D₀ (s i)`, `collarWidth (n i) ≤ s i` | identical |
| (3) `dist_∞(T_i, Z) > 2 n_i^β`, `dist_∞(T_i, ⋃_{j < i, f_j = f_i} X_j) > 2 n_i^β`, `β = 1 - 2·10⁻⁶`, distance to the empty set infinite | the two `ambientEDist` clauses with `ofReal (2 n^(1 - 2/1000000))` | identical |
| (4) `Σ n_i^{-100} ≤ C b` | same | identical |

## Lemmas 2.1, 3.1, 3.2 and Proposition 3.3

These are internal to the proof (the paper exports only the results above in §1.3). Their
statements follow the paper's equations (2.1), (3.1), (3.2), (3.9) and (3.21) with the
conventions of `RefactoringResult.md` §2 and §5; in particular Lemma 2.1 carries the explicit
absolute constant `4`, and Proposition 3.3 unfolds the supremum `F_box` into a universally
quantified bound. They do not affect the faithfulness of Theorem 1.1, which depends on them only
through the propositions above.

## Summary

No clause of Theorem 1.1, Corollary 1.2 or of the exported propositions is weakened in Lean.
Three places are strictly stronger than the paper (no uniqueness hypothesis in Theorem 1.1,
arbitrary anchors in Proposition 4.3, arbitrary `D₀` and `C_tpl` in Proposition 11.2). One clause
is omitted with a stated justification (`L + 2r = o(n^β)` in Proposition 10.2). One convention is
fixed where the paper's wording allows a degenerate reading (template pieces are nondegenerate),
in agreement with the convention TNLean records for the same definition, and it does not enter
the statement of Theorem 1.1.
