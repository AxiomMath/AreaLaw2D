import AreaLaw.S03_InitialBox
import AreaLaw.S04_Quasilocal
import AreaLaw.S08_Comparators

/-!
# §9 Scales and the statements shared between the subsection files

Digest `digest/09-scanner.md`. The scales of D9.2 and the test geometry of D9.3, and the anchors
one subsection file cites from another, stated as `Prop`s so that the files can be written in
parallel: Proposition 9.2 (`Prop_9_2`, consumed by Propositions 9.5 and 9.6), Lemma 9.4
(`Lemma_9_4`, consumed by Propositions 9.5 and 9.6) and Proposition 9.5 (`Prop_9_5`, consumed by
Proposition 9.6). `S09_Scanner.lean` discharges each with the declaration of its anchor.

Proposition 9.2 is graph-level (Map.md, Dimension: `any d`): a simple graph `G` on a site type
`σ` with polynomial ball growth, and the ambient depth `dist_∞(·, T)` replaced by any depth
function `dep : σ → ℕ` that changes by at most one along an edge (on `ℤ²`, `dist_∞(·, T)`, with
`T = {dep = 0}`). Lemma 9.4 and Proposition 9.5 are stated on `ℤ × ℤ`, the encoding of the frozen
`IsTemplate` and `F_box`.
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix Filter Topology Arealaw Finset
open OpenAI (pureState HasGlobalGap IsTemplate IsSeparatedFromCut ambientDilation)

namespace AreaLaw.Scanner

universe u

/-! ## D9.2 Target, collar and scales -/

/-- D9.2. The collar depth `L = ⌊n^{1-ℓ}⌋`. -/
noncomputable def L (ℓ : ℝ) (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 - ℓ)⌋₊

/-- D9.2. The window scale and number of offsets `m = ⌊n^μ⌋`. -/
noncomputable def m (μ : ℝ) (n : ℕ) : ℕ := ⌊(n : ℝ) ^ μ⌋₊

/-- D9.2. The number of bands `K = ⌊L/(8m)⌋`. -/
noncomputable def K (ℓ μ : ℝ) (n : ℕ) : ℕ := L ℓ n / (8 * m μ n)

/-- D9.2. The charge lookahead `D = ⌈n^κ⌉`. -/
noncomputable def D (κ : ℝ) (n : ℕ) : ℕ := ⌈(n : ℝ) ^ κ⌉₊

/-- D9.2. The per-band metric weight `a = W/K` (so `W = aK` is the total weight). -/
noncomputable def a (ℓ μ W : ℝ) (n : ℕ) : ℝ := W / K ℓ μ n

/-- D9.3. The graph radius of the splitting supports, `r₀ = ⌈C₁ (log n)²⌉` (Proposition 4.5). -/
noncomputable def r₀ (C₁ : ℝ) (n : ℕ) : ℕ := ⌈C₁ * Real.log n ^ 2⌉₊

/-! ## D9.3 Test geometry -/

section TestGeometry

variable {σ : Type u} [DecidableEq σ] (G : SimpleGraph σ) [DecidableRel G.Adj]

/-- D9.3 (`scanner:test-geometry`), graph-level. `dep` is the depth (`dist_∞(·, T)` on `ℤ²`),
changing by at most one along an edge; `|T| ≤ C_T n²`; every positive-depth row
`T_j \ T_{j-1}` (`1 ≤ j ≤ L`) has at most `n` sites; `dist_∞(T, Z) > 2L + 10 r₀`. Rows and the
target are counted inside `Λ`. -/
structure TestGeometry (Λ A : Finset σ) (dep : σ → ℕ) (CT : ℝ) (n L r₀ : ℕ) : Prop where
  lipschitz : ∀ x y, G.Adj x y → dep x ≤ dep y + 1
  card_target : (#(Λ.filter fun x => dep x = 0) : ℝ) ≤ CT * (n : ℝ) ^ 2
  card_row : ∀ j, 1 ≤ j → j ≤ L → #(Λ.filter fun x => dep x = j) ≤ n
  clearance : ∀ z ∈ GraphDomain.cutEndpoints G Λ A, 2 * L + 10 * r₀ < dep z

end TestGeometry

/-- The physical region `Q ⊆ Λ` of a region `Q` of the domain type `↥Λ`. -/
def up {σ : Type u} [DecidableEq σ] {Λ : Finset σ} (Q : Finset Λ) : Finset σ :=
  Q.map (Function.Embedding.subtype (· ∈ Λ))

theorem up_subset {σ : Type u} [DecidableEq σ] {Λ : Finset σ} (Q : Finset Λ) : up Q ⊆ Λ := by
  intro x hx
  obtain ⟨y, -, rfl⟩ := Finset.mem_map.1 hx
  exact y.2

/-! ## Proposition 9.2 -/

open Comparators in
/-- D9.9 **Proposition 9.2** (the scanner estimate), in the form consumed by Propositions 9.5
and 9.6: the selected point is any tree `T` over the status collection (in `prop_9_2` it is the
terminal tree of the selected charge round at the selected `p_k ∈ [ε/2, ε]`).

Assume `scanner:scales` (`0 < ℓ < 1`, `0 < κ < μ < 1 - ℓ`), `scanner:test-geometry`,
`0 < e < 1`, `κ ≤ e`, `S_Ω(X) ≤ C_e n^{1+e}`, `S_Ω(Q_j) ≤ C_e (n L^e + n)` (`0 ≤ j ≤ L`),
`ε = n^{-ν}`, `a (r₀+1)^{m₀}` small (`a r₀²` on `ℤ²`, D9.11.4: the split supports are
`r₀`-balls, of `log`-dimension `≤ C (r₀+1)^{m₀}`). Then the truncated system `Ω̃` (D4.11), the
auxiliary systems, the label sector and `pre` of Proposition 8.1 (width `w = n^{3/5}`) and the
statuses of the scan satisfy: every entropy and mutual information of `Ω̃` is within
`n^{-200}(1 + |Q|)` of that of
`Ω` (D9.9.1); `z ≥ 1 - n^{-100}`; prefix data with `B_sh ≤ C(nL^e + n)`, `B_exc ≤ C n D`; marginal
moment data with `𝓑 ≤ C n D (log n)^C`; `Λ \ S₀ ⊆ V` in every status (D9.28.2); all norm
comparisons of Proposition 8.1; and for every `k ≥ 1` a point with
`E_def,k ≤ C n^ℓ D² W² (log n)^C (δ_n^{1/8} + ε + n^{-100}) + C n^{-1000} + o_k(1)`,
`δ_n = C ε^{-1} (n^{e-μ} + a^{1/4} (log n)^C)`. The finite system, `n`, the scan and all
auxiliary dimensions are fixed before `k → ∞`; constants depend on the exponents, `C_e`, `C_T`
and the Hamiltonian parameters, not on `W`, `Λ`, `A`, `dep`. -/
def Prop_9_2 : Prop :=
  ∀ {σ : Type u} [DecidableEq σ] [Nonempty σ] (G : SimpleGraph σ) [DecidableRel G.Adj]
    (V : ℕ → ℕ),
    (∀ (Λ : Finset σ) (x : σ) (r : ℕ), #(GraphDomain.ball G Λ x r) ≤ V r) →
    ∀ (K₀ : ℝ) (m₀ : ℕ), 0 ≤ K₀ → (∀ r : ℕ, (V r : ℝ) ≤ K₀ * (r + 1) ^ m₀) →
    ∀ (q : ℕ) [NeZero q] (R : ℕ) (J Δ : ℝ), 0 < Δ →
    ∀ (ℓ κ μ ν e Ce CT : ℝ), 0 < ℓ → ℓ < 1 → 0 < κ → κ < μ → μ < 1 - ℓ → 0 < ν →
      0 < e → e < 1 → κ ≤ e → 0 < Ce → 0 < CT →
    ∃ (C₁ c Crl csh Csu Csl C₀ c₀ C Cl : ℝ) (n₀ : ℕ), 0 < C₁ ∧ 0 < c ∧ 0 < csh ∧ 0 < Csl ∧
      0 < Csu ∧ 0 < Crl ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ W : ℝ, 1 ≤ W → a ℓ μ W n * ((r₀ C₁ n : ℝ) + 1) ^ m₀ ≤ c →
      ∀ (Λ : Finset σ)
        (Φ : (X : Finset σ) → Matrix (Reg (fun _ : σ => Fin q) X) (Reg (fun _ : σ => Fin q) X) ℂ),
        GraphDomain.IsAdmissible G Λ R J Φ →
      ∀ (Ω : Reg (fun _ : σ => Fin q) Λ → ℂ) (hΩ : star Ω ⬝ᵥ Ω = 1) (E₀ : ℝ),
        GraphDomain.hamiltonian Λ Φ *ᵥ Ω = (E₀ : ℂ) • Ω →
        HasGlobalGap (GraphDomain.hamiltonian Λ Φ) Ω E₀ Δ →
      ∀ (A : Finset σ) (hA : A ⊆ Λ) (dep : σ → ℕ),
        TestGeometry G Λ A dep CT n (L ℓ n) (r₀ C₁ n) →
        (pureState Ω hΩ).regionEntropy
            ((filter_subset _ A).trans hA : A.filter (fun x => dep x = 0) ⊆ Λ) ≤
          Ce * (n : ℝ) ^ (1 + e) →
        (∀ j ≤ L ℓ n, (pureState Ω hΩ).regionEntropy
            ((filter_subset _ A).trans hA : A.filter (fun x => 0 < dep x ∧ dep x ≤ j) ⊆ Λ) ≤
          Ce * ((n : ℝ) * (L ℓ n : ℝ) ^ e + n)) →
      ∃ (Dt : PhysData (fun _ : Λ => q))
        (E : TypicalSet Dt ((A.filter fun x => dep x = 0).subtype (· ∈ Λ)))
        (St : Type) (_ : Fintype St) (_ : DecidableEq St)
        (Γ : Statuses Λ (K ℓ μ n) St ((A.filter fun x => dep x = 0).subtype (· ∈ Λ)))
        (l : ∀ k : ℕ, IrrepLabel (Equiv.Perm (Fin k))) (𝓡 : Finset (Finset Λ))
        (Bsh Bexc 𝓑 : ℝ),
        -- D9.9.1: transfer `Ω → Ω̃`
        (∀ Q : Finset Λ,
          |Dt.S Q - (pureState Ω hΩ).regionEntropy (up_subset Q)| ≤
            (n : ℝ) ^ (-200 : ℝ) * (1 + #Q)) ∧
        (∀ Q Q' : Finset Λ, Disjoint Q Q' →
          |Dt.I Q Q' - (pureState Ω hΩ).mutualInfo (up_subset Q) (up_subset Q')| ≤
            (n : ℝ) ^ (-200 : ℝ) * (1 + #Q)) ∧
        -- D9.9.2: comparator data
        E.w = (n : ℝ) ^ (3 / 5 : ℝ) ∧ 1 - (n : ℝ) ^ (-100 : ℝ) ≤ E.z ∧
        PrefixData Dt Γ 𝓡 Bsh Bexc ∧ Bsh ≤ C * ((n : ℝ) * (L ℓ n : ℝ) ^ e + n) ∧
        Bexc ≤ C * n * D κ n ∧
        MgfData Dt Γ C₀ c₀ 𝓑 ∧ 𝓑 ≤ C * n * D κ n * Real.log n ^ Cl ∧
        -- D9.28.2: the far region contains `Λ \ S₀`
        (∀ s g, (Λ \ A.filter fun x => dep x ≤ L ℓ n).subtype (· ∈ Λ) ⊆ Γ.V s g) ∧
        -- the norm comparisons of Proposition 8.1
        RoughUpper Dt Γ E (a ℓ μ W n) l Bsh Bexc ∧
        (∀ τ : ℝ, 0 < τ → τ < 1 / 2 → RoughLower Dt Γ E Crl (a ℓ μ W n) τ l) ∧
        (a ℓ μ W n ≤ csh / Real.sqrt 𝓑 → SharpUpper Dt Γ E Csu (a ℓ μ W n) 𝓑 l ∧
          ∀ τ : ℝ, 0 < τ → τ < 1 / 2 → SharpLower Dt Γ E Csl (a ℓ μ W n) τ 𝓑 l) ∧
        -- the selected point
        ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧ ∀ k : ℕ, 0 < k →
          ∃ T : Transport.MeanTree St,
            Edef Dt Γ E T (a ℓ μ W n) k (l k) ≤
              C * (n : ℝ) ^ ℓ * (D κ n : ℝ) ^ 2 * W ^ 2 * Real.log n ^ Cl *
                  ((C * (n : ℝ) ^ ν * ((n : ℝ) ^ (e - μ) +
                      a ℓ μ W n ^ (1 / 4 : ℝ) * Real.log n ^ Cl)) ^ (1 / 8 : ℝ) +
                    (n : ℝ) ^ (-ν) + (n : ℝ) ^ (-100 : ℝ)) +
                C * (n : ℝ) ^ (-1000 : ℝ) + r k

/-! ## Lemma 9.4 -/

/-- D9.15 **Lemma 9.4** (rows, coverings and shell entropy). For `C_tpl` large there is a
numerical `C` such that every template `T` with parameters `(n, s₀)` has `|T| ≤ C n s₀`,
`|T_j \ T_{j-1}| ≤ n` (`1 ≤ j ≤ s₀`), `|∂_{ℤ²} T_j| ≤ C n` (`0 ≤ j ≤ s₀`). If moreover `T` is
separated from the cut and `F_box(r) ≤ C_e r^{1+e}` for all `r ≥ 1` (`0 < e < 1`), then for every
`1 ≤ L ≤ s₀`: `S_Ω(X) ≤ C'_e n s₀^e`, `S_Ω(Q_j) ≤ C'_e n L^e` (`0 ≤ j ≤ L`); the same shell bound
with an extra `n log q` holds for every prefix of all depth rows before one row and a subset of
that row; the physical cuts of `X`, `Q_j`, `A ∩ T_j` (`j ≤ s₀`) have at most `C n` edges.
`C'_e` depends only on `e`, `C_e`. 2D only: templates are unions of planar pieces of slopes
`0, ∞, ±1`. -/
def Lemma_9_4 : Prop :=
  ∃ Ctpl₀ : ℝ, ∀ Ctpl : ℝ, Ctpl₀ ≤ Ctpl → ∃ C : ℝ, 0 < C ∧
    (∀ (n s₀ : ℕ) (T : Finset (ℤ × ℤ)), IsTemplate Ctpl n s₀ T →
      (#T : ℝ) ≤ C * n * s₀ ∧
      (∀ j, 1 ≤ j → j ≤ s₀ → #(ambientDilation T j \ ambientDilation T (j - 1)) ≤ n) ∧
      ∀ j ≤ s₀, (#(GraphDomain.edgeBoundary squareLattice (ambientDilation T (j + 1))
        (ambientDilation T j)) : ℝ) ≤ C * n) ∧
    ∀ (q R : ℕ) (J Δ e Ce : ℝ), 0 < e → e < 1 → 0 < Ce →
    ∃ Ce' : ℝ, 0 < Ce' ∧ ∀ D₀ : ℝ, 2 * R + 10 < D₀ →
      (∀ r : ℕ, 1 ≤ r → F_box q R J Δ r ≤ Ce * (r : ℝ) ^ (1 + e)) →
      ∀ (Λ : Finset (ℤ × ℤ))
        (Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (OpenAI.Qudits q) X) (Reg (OpenAI.Qudits q) X) ℂ),
        OpenAI.IsAdmissible Λ R J Φ →
      ∀ (Ω : Reg (OpenAI.Qudits q) Λ → ℂ) (hΩ : star Ω ⬝ᵥ Ω = 1) (E₀ : ℝ),
        OpenAI.hamiltonian Λ Φ *ᵥ Ω = (E₀ : ℂ) • Ω →
        HasGlobalGap (OpenAI.hamiltonian Λ Φ) Ω E₀ Δ →
      ∀ (A : Finset (ℤ × ℤ)) (hA : A ⊆ Λ) (T : Finset (ℤ × ℤ)) (n s₀ : ℕ),
        IsTemplate Ctpl n s₀ T → IsSeparatedFromCut D₀ s₀ Λ A T →
        (pureState Ω hΩ).regionEntropy (inter_subset_left.trans hA : A ∩ T ⊆ Λ) ≤
          Ce' * n * (s₀ : ℝ) ^ e ∧
        (∀ L' : ℕ, 1 ≤ L' → L' ≤ s₀ → ∀ j ≤ L',
          (pureState Ω hΩ).regionEntropy
              (inter_subset_left.trans hA : A ∩ (ambientDilation T j \ T) ⊆ Λ) ≤
            Ce' * n * (L' : ℝ) ^ e ∧
          ∀ (Z : Finset (ℤ × ℤ))
            (hZ : Z ⊆ A ∩ (ambientDilation T (j + 1) \ ambientDilation T j)),
            (pureState Ω hΩ).regionEntropy
                (union_subset (inter_subset_left.trans hA) ((hZ.trans inter_subset_left).trans hA) :
                  A ∩ (ambientDilation T j \ T) ∪ Z ⊆ Λ) ≤
              Ce' * n * (L' : ℝ) ^ e + n * Real.log q) ∧
        ∀ j ≤ s₀,
          (#(OpenAI.edgeBoundary Λ (A ∩ T)) : ℝ) ≤ C * n ∧
          (#(OpenAI.edgeBoundary Λ (A ∩ (ambientDilation T j \ T))) : ℝ) ≤ C * n ∧
          (#(OpenAI.edgeBoundary Λ (A ∩ ambientDilation T j)) : ℝ) ≤ C * n

/-! ## Proposition 9.5 -/

/-- D9.19 **Proposition 9.5** (improved safe-box estimate). There is `C` depending only on
`q, R, J, Δ` with `F_box(r) ≤ C r^{1+e_*}` (`r ≥ 1`), `e_* = 2·10⁻⁶`. -/
def Prop_9_5 : Prop :=
  ∀ (q R : ℕ) (J Δ : ℝ), 1 ≤ q → 0 < J → 0 < Δ →
    ∃ C : ℝ, ∀ r : ℕ, 1 ≤ r → F_box q R J Δ r ≤ C * (r : ℝ) ^ (1 + (2 / 1000000 : ℝ))

end AreaLaw.Scanner
