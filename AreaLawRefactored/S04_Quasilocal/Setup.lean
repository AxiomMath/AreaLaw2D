import AreaLawRefactored.S02_Preliminaries

/-!
# §4.0 Setup: anchors, graph balls, the conditional expectation `E_{i,l}`

Digest `digest/04-quasilocal.md` (D4.1–D4.3), paper `paper/sections/03-quasilocal.tex`
lines 14–41. Graph-level (`Map.md`, Dimension): a simple graph `G` on a site type `σ`, the
induced distance `d_Λ`, ball growth `V`.
-/

namespace AreaLaw

open Arealaw Matrix
open OpenAI (condExpect IsSupportedOn)
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

/-- §4 notation. The Heisenberg evolution `τ_t(B) = e^{itH} B e^{-itH}`. -/
noncomputable def τ {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (t : ℝ)
    (B : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  NormedSpace.exp ((t * Complex.I) • H) * B * NormedSpace.exp ((-(t * Complex.I)) • H)

namespace GraphDomain

variable {σ : Type*} [DecidableEq σ] (G : SimpleGraph σ)

/-! ## D4.1 Anchored decomposition and graph balls -/

theorem graphNbhd_subset (Λ S : Finset σ) (r : ℕ) : graphNbhd G Λ S r ⊆ Λ :=
  Finset.filter_subset _ _

/-- D4.1. The connected component of the anchor `a` in the graph induced on `Λ`. -/
noncomputable def component (Λ : Finset σ) (a : σ) : Finset σ :=
  Λ.filter fun x => domainEDist G Λ a x ≠ ⊤

theorem component_subset (Λ : Finset σ) (a : σ) : component G Λ a ⊆ Λ :=
  Finset.filter_subset _ _

/-- D4.1. `H = ∑_{i ∈ 𝓘} h_i`, `i` indexing the distinct nonempty designated supports `X_i`;
an anchor `a_i ∈ X_i` is fixed; `N_l(a) = {x ∈ Λ : d_Λ(a,x) ≤ l}` (`ball G Λ a l`).  Standing:
`diam_{d_Λ} X_i ≤ R`, `‖h_i‖ ≤ J`; so `X_i ⊆ N_R(a_i)`. -/
theorem step_4_1 {Λ X : Finset σ} {R : ℕ} {a : σ} (hX : X ∈ supports G Λ R) (ha : a ∈ X) :
    X ⊆ ball G Λ a R :=
  subset_ball_of_mem_supports G hX ha

/-! ## D4.2 The conditional expectation onto a ball -/

variable {loc : σ → Type*} [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)]

/-- D4.2 (eq:quasilocal-ce). With `Y = Λ \ N_l(a_i)`,
`E_{i,l}(B) = q^{-|Y|} Tr_Y(B) ⊗ I_Y`, tensor factors at their original sites. -/
noncomputable def E (Λ : Finset σ) (a : σ) (l : ℕ) (B : Matrix (Reg loc Λ) (Reg loc Λ) ℂ) :
    Matrix (Reg loc Λ) (Reg loc Λ) ℂ :=
  condExpect (graphNbhd_subset G Λ {a} l) B

variable {G}

theorem E_sub (Λ : Finset σ) (a : σ) (l : ℕ) (A B : Matrix (Reg loc Λ) (Reg loc Λ) ℂ) :
    E G Λ a l (A - B) = E G Λ a l A - E G Λ a l B := by
  simp only [E, condExpect]
  rw [ptrace_sub, sub_eq_add_neg (ptrace _ A), ← neg_one_smul ℂ (ptrace _ B), extendId_add,
    extendId_smul, smul_add, smul_comm _ (-1 : ℂ), neg_one_smul, ← sub_eq_add_neg]

/-- D4.2. The range of `E_{i,l}` lies in the algebra on `N_l(a_i)`. -/
theorem isSupportedOn_E (Λ : Finset σ) (a : σ) (l : ℕ) (B : Matrix (Reg loc Λ) (Reg loc Λ) ℂ) :
    IsSupportedOn (graphNbhd_subset G Λ {a} l) (E G Λ a l B) :=
  ⟨(Fintype.card (Reg loc (Λ \ graphNbhd G Λ {a} l)) : ℂ)⁻¹ •
    ptrace (graphNbhd_subset G Λ {a} l) B, (extendId_smul _ _ _).symm⟩

section Nonempty

variable [∀ i, Nonempty (loc i)]

/-- D4.2. `E_{i,l}` fixes every operator supported in `N_l(a_i)`. -/
theorem E_extendId (Λ : Finset σ) (a : σ) (l : ℕ)
    (A : Matrix (Reg loc (graphNbhd G Λ {a} l)) (Reg loc (graphNbhd G Λ {a} l)) ℂ) :
    E G Λ a l (extendId (graphNbhd_subset G Λ {a} l) A) =
      extendId (graphNbhd_subset G Λ {a} l) A := by
  have hp := ptrace_mul_extendId (graphNbhd_subset G Λ {a} l)
    (1 : Matrix (Reg loc Λ) (Reg loc Λ) ℂ) A
  simp only [one_mul, ptrace_one, smul_mul, one_mul] at hp
  simp only [E, condExpect, hp, extendId_smul, smul_smul]
  rw [inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_smul]

/-- D4.2. `E_{i,l}` is positive, unital, and fixes every operator supported in `N_l(a_i)`;
hence `0 ≤ B ≤ I ⇒ 0 ≤ E_{i,l} B ≤ I`. -/
theorem eq_quasilocal_ce (Λ : Finset σ) (a : σ) (l : ℕ) :
    E G Λ a l (1 : Matrix (Reg loc Λ) (Reg loc Λ) ℂ) = 1 ∧
    (∀ B : Matrix (Reg loc Λ) (Reg loc Λ) ℂ, 0 ≤ B → 0 ≤ E G Λ a l B) ∧
    (∀ B : Matrix (Reg loc Λ) (Reg loc Λ) ℂ, 0 ≤ B → B ≤ 1 →
      0 ≤ E G Λ a l B ∧ E G Λ a l B ≤ 1) ∧
    ∀ B : Matrix (Reg loc Λ) (Reg loc Λ) ℂ,
      IsSupportedOn (graphNbhd_subset G Λ {a} l) B → E G Λ a l B = B := by
  have hpos : ∀ B : Matrix (Reg loc Λ) (Reg loc Λ) ℂ, 0 ≤ B → 0 ≤ E G Λ a l B := by
    intro B hB
    rw [Matrix.le_iff] at hB ⊢
    simp only [sub_zero] at hB ⊢
    exact (posSemidef_extendId _ (posSemidef_ptrace _ hB)).smul (by positivity)
  have hfix : ∀ B : Matrix (Reg loc Λ) (Reg loc Λ) ℂ,
      IsSupportedOn (graphNbhd_subset G Λ {a} l) B → E G Λ a l B = B := by
    rintro _ ⟨A, rfl⟩
    exact E_extendId Λ a l A
  have h1 : E G Λ a l (1 : Matrix (Reg loc Λ) (Reg loc Λ) ℂ) = 1 := by
    simpa using hfix 1 ⟨1, (extendId_one _).symm⟩
  refine ⟨h1, hpos, fun B h0 h1' => ⟨hpos B h0, ?_⟩, hfix⟩
  have := hpos (1 - B) (sub_nonneg.2 h1')
  rwa [E_sub, h1, sub_nonneg] at this

end Nonempty

/-! ## D4.11 The variable-radius truncation (definitions)

`eq:quasilocal-variable-radius`: `d_i^0 = d_Λ(a_i, S₀)`, `r_i = max {r₀, ⌊d_i^0/2⌋}`,
`h̃_i = k_{i,r_i}`, `X̃_i = N_{r_i}(a_i)` if `d_i^0 < ∞`; `h̃_i = k_i` and `X̃_i` the component
of `a_i` if `d_i^0 = ∞`. -/

variable (G)

/-- D4.11. `d_Λ(x, S₀) = min_{y ∈ S₀} d_Λ(x, y)` (`⊤` for `S₀ = ∅`). -/
noncomputable def setDist (Λ S₀ : Finset σ) (x : σ) : ℕ∞ :=
  S₀.inf fun y => domainEDist G Λ x y

/-- D4.11. `r_i = max {r₀, ⌊d_i^0 / 2⌋}`. -/
def radius (r₀ d : ℕ) : ℕ := max r₀ (d / 2)

/-- D4.11. The truncated constraint `h̃_i`: `k_{i,r_i}` at finite distance from `S₀`, `k_i`
otherwise. -/
noncomputable def truncated (Λ S₀ : Finset σ) (r₀ : ℕ) (a : σ)
    (k : Matrix (Reg loc Λ) (Reg loc Λ) ℂ) : Matrix (Reg loc Λ) (Reg loc Λ) ℂ :=
  if setDist G Λ S₀ a = ⊤ then k else E G Λ a (radius r₀ (setDist G Λ S₀ a).toNat) k

/-- D4.11. The truncated support `X̃_i`: `N_{r_i}(a_i)` at finite distance from `S₀`, the
component of `a_i` otherwise. -/
noncomputable def truncatedSupport (Λ S₀ : Finset σ) (r₀ : ℕ) (a : σ) : Finset σ :=
  if setDist G Λ S₀ a = ⊤ then component G Λ a
  else ball G Λ a (radius r₀ (setDist G Λ S₀ a).toNat)

end GraphDomain

/-! ## D4.3 Counting budget -/

section D43

open Finset GraphDomain

variable {σ : Type*} [DecidableEq σ] (G : SimpleGraph σ) (V : ℕ → ℕ)
  (hV : ∀ (Λ : Finset σ) (x : σ) (r : ℕ), #(ball G Λ x r) ≤ V r)

include hV in
/-- D4.3 (eq:quasilocal-budget). `sup_{x ∈ Λ} ∑_{i : x ∈ X_i} ‖h_i‖ ≤ b₀ := J μ_R`,
`|X_i| ≤ v_R`; at most `μ_R` labels share any anchor. -/
theorem step_4_3 {loc : σ → Type} [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)]
    (Λ : Finset σ) (R : ℕ) (J : ℝ) (Φ : (X : Finset σ) → Matrix (Reg loc X) (Reg loc X) ℂ)
    (hΦ : IsAdmissible G Λ R J Φ) (a : Finset σ → σ) (ha : ∀ X ∈ supports G Λ R, a X ∈ X) :
    (∀ x, ∑ X ∈ supports G Λ R with x ∈ X, ‖Φ X‖ ≤ J * μ V R) ∧
    (∀ X ∈ supports G Λ R, #X ≤ V R) ∧
    ∀ x, #{X ∈ supports G Λ R | a X = x} ≤ μ V R :=
  -- D2.8
  ⟨fun x => (step_2_8 G V hV Λ R x).2.2.1 J Φ hΦ,
    fun X hX => (step_2_8 G V hV Λ R (a X)).2.2.2 X hX,
    fun x => (step_2_8 G V hV Λ R x).2.1 a ha⟩

end D43

/-! ## The square lattice -/

theorem domainComponent_eq_graph : OpenAI.domainComponent = GraphDomain.component squareLattice :=
  rfl

end AreaLaw
