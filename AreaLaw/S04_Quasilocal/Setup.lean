import AreaLaw.S02_Preliminaries
import AreaLawForMathlib.Analysis.Matrix.WeylTwirl

/-!
# §4.0 Setup: anchors, graph balls, the conditional expectation `E_{i,l}`

Digest `digest/04-quasilocal.md` (D4.1–D4.3), paper `paper/sections/03-quasilocal.tex`
lines 14–41. Graph-level (`Map.md`, Dimension): a simple graph `G` on a site type `σ`, the
induced distance `d_Λ`, ball growth `V`.

Some declarations here come from the v1 file `OpenAI/ConditionalExpectation.lean`, whose header
records it as ported or adapted from `LionSR/QICLean` and `LionSR/TNLean` (see `NOTICE`).
-/

namespace AreaLaw

open Arealaw Matrix
open OpenAI (condExpect IsSupportedOn)
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator Kronecker

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

/-- Extension by the identity does not increase the operator norm. -/
theorem norm_extendId_le {Λ X : Finset σ} (hX : X ⊆ Λ)
    (A : Matrix (Reg loc X) (Reg loc X) ℂ) : ‖extendId hX A‖ ≤ ‖A‖ := by
  rw [extendId_eq_kronecker]
  exact (l2_opNorm_submatrix_le _ (Equiv.injective _) (Equiv.injective _)).trans
    (l2_opNorm_kronecker_one_le A)

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

/-! ### D4.2 contractivity and the twirl bound

`E_{i,l}` is the uniform average of the conjugations by the Weyl operators `1 ⊗ W` on
`Y = Λ \ N_l(a_i)` (`Matrix.complementaryWeylTwirl`), the finite form of the Haar twirl
`∏_{y ∈ Y} T_y`. -/

section Twirl

variable {S T : Finset σ}

omit [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] [∀ i, Nonempty (loc i)] in
private theorem restr_sdiff_sdiff_glue (h : S ⊆ T) (x : Reg loc S) (z : Reg loc (T \ S)) :
    restr (S := T \ (T \ S)) Finset.sdiff_subset (glue x z) =
      regEquivOfEq (Finset.sdiff_sdiff_eq_self h).symm x := by
  funext j
  have hj : (j : σ) ∈ S := by simpa [Finset.sdiff_sdiff_eq_self h] using j.2
  simp [restr, glue, hj, Finset.restrict₂]

omit [∀ i, Fintype (loc i)] [∀ i, Nonempty (loc i)] in
private theorem extendId_sdiff_submatrix_glueEquiv (h : S ⊆ T)
    (A : Matrix (Reg loc (T \ S)) (Reg loc (T \ S)) ℂ) :
    (extendId (Finset.sdiff_subset : T \ S ⊆ T) A).submatrix (glueEquiv h) (glueEquiv h) =
      (1 : Matrix (Reg loc S) (Reg loc S) ℂ) ⊗ₖ A := by
  ext ⟨x, z⟩ ⟨x', z'⟩
  simp only [submatrix_apply, glueEquiv_apply, extendId, of_apply, kroneckerMap_apply,
    restr_sdiff_sdiff_glue h, (regEquivOfEq _).injective.eq_iff, restr_glue_compl, one_apply]
  split_ifs <;> simp

private noncomputable def regZModEquiv (C : Type*) [Fintype C] [Nonempty C] :
    C ≃ ZMod (Fintype.card C) :=
  (Fintype.equivFin C).trans (ZMod.finEquiv (Fintype.card C)).toEquiv

private noncomputable def regWeylRoot (C : Type*) [Fintype C] : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / Fintype.card C)

private theorem isPrimitiveRoot_regWeylRoot (C : Type*) [Fintype C] [Nonempty C] :
    IsPrimitiveRoot (regWeylRoot C) (Fintype.card C) :=
  Complex.isPrimitiveRoot_exp _ Fintype.card_ne_zero

/-- D4.2. In product coordinates `S | T \ S`, the normalized conditional expectation is the
complementary Weyl twirl. -/
theorem condExpect_submatrix_eq_complementaryWeylTwirl (h : S ⊆ T)
    (B : Matrix (Reg loc T) (Reg loc T) ℂ) :
    (condExpect h B).submatrix (glueEquiv h) (glueEquiv h) =
      Matrix.complementaryWeylTwirl (regZModEquiv (Reg loc (T \ S)))
        (regWeylRoot (Reg loc (T \ S))) (B.submatrix (glueEquiv h) (glueEquiv h)) := by
  have : NeZero (Fintype.card (Reg loc (T \ S))) := ⟨Fintype.card_ne_zero⟩
  rw [Matrix.complementaryWeylTwirl_eq_smul_traceRight_kronecker_one _
    (isPrimitiveRoot_regWeylRoot _)]
  ext ⟨x, z⟩ ⟨y, w⟩
  simp only [Matrix.submatrix_apply, glueEquiv_apply, condExpect, Matrix.smul_apply,
    extendId_apply_glue, Matrix.kronecker_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hzw : z = w
  · subst w
    simp only [if_pos, mul_one]
    rfl
  · simp [hzw]

/-- D4.2. The normalized conditional expectation is contractive: `‖E B‖ ≤ ‖B‖`. -/
theorem norm_condExpect_le (h : S ⊆ T) (B : Matrix (Reg loc T) (Reg loc T) ℂ) :
    ‖condExpect h B‖ ≤ ‖B‖ := by
  have : NeZero (Fintype.card (Reg loc (T \ S))) := ⟨Fintype.card_ne_zero⟩
  rw [← l2_opNorm_submatrix (condExpect h B) (glueEquiv h) (glueEquiv h),
    condExpect_submatrix_eq_complementaryWeylTwirl h B,
    ← l2_opNorm_submatrix B (glueEquiv h) (glueEquiv h)]
  exact Matrix.norm_complementaryWeylTwirl_le _ (isPrimitiveRoot_regWeylRoot _) _

/-- D4.2. `E_{i,l}` is contractive in operator norm. -/
theorem norm_E_le (Λ : Finset σ) (a : σ) (l : ℕ) (B : Matrix (Reg loc Λ) (Reg loc Λ) ℂ) :
    ‖E G Λ a l B‖ ≤ ‖B‖ :=
  norm_condExpect_le _ B

/-- D4.4.9. `‖B - E B‖ ≤ sup_U ‖[B, U]‖` over the contractions `U` supported in `T \ S`. -/
theorem norm_sub_condExpect_le (h : S ⊆ T) (B : Matrix (Reg loc T) (Reg loc T) ℂ) (ε : ℝ)
    (hcomm : ∀ U : Matrix (Reg loc T) (Reg loc T) ℂ,
      IsSupportedOn (Finset.sdiff_subset : T \ S ⊆ T) U → ‖U‖ ≤ 1 → ‖B * U - U * B‖ ≤ ε) :
    ‖B - condExpect h B‖ ≤ ε := by
  have : NeZero (Fintype.card (Reg loc (T \ S))) := ⟨Fintype.card_ne_zero⟩
  have hζ := isPrimitiveRoot_regWeylRoot (Reg loc (T \ S))
  rw [← l2_opNorm_submatrix (B - condExpect h B) (glueEquiv h) (glueEquiv h)]
  change ‖B.submatrix (glueEquiv h) (glueEquiv h) -
    (condExpect h B).submatrix (glueEquiv h) (glueEquiv h)‖ ≤ ε
  rw [condExpect_submatrix_eq_complementaryWeylTwirl h B]
  refine Matrix.norm_sub_complementaryWeylTwirl_le _ hζ _ _ fun a b => ?_
  let W := Matrix.reindexedWeyl (regZModEquiv (Reg loc (T \ S)))
    (regWeylRoot (Reg loc (T \ S))) a b
  let U := extendId (Finset.sdiff_subset : T \ S ⊆ T) W
  have hU : ‖U‖ ≤ 1 := (norm_extendId_le _ W).trans_eq
    (CStarRing.norm_of_mem_unitary (Matrix.reindexedWeyl_mem_unitary _ hζ a b))
  have hb := hcomm U ⟨W, rfl⟩ hU
  rw [← l2_opNorm_submatrix (B * U - U * B) (glueEquiv h) (glueEquiv h)] at hb
  change ‖(B * U).submatrix (glueEquiv h) (glueEquiv h) -
    (U * B).submatrix (glueEquiv h) (glueEquiv h)‖ ≤ ε at hb
  rw [← Matrix.submatrix_mul_equiv B U (glueEquiv h) (glueEquiv h) (glueEquiv h),
    ← Matrix.submatrix_mul_equiv U B (glueEquiv h) (glueEquiv h) (glueEquiv h),
    show U.submatrix (glueEquiv h) (glueEquiv h) = 1 ⊗ₖ W from
      extendId_sdiff_submatrix_glueEquiv h W] at hb
  exact hb

end Twirl

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
