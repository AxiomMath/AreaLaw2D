import AreaLaw.S04_Quasilocal.Locality
import AreaLawForMathlib.Analysis.CStarAlgebra.SqrtHolder

/-!
# §4.2 Proposition 4.3: positive replacement of the Hamiltonian (D4.6)

Digest `digest/04-quasilocal.md` (D4.6), paper `paper/sections/03-quasilocal.tex` lines 220–329.
Graph-level (`Map.md`, Dimension): a simple graph `G` on a site type `σ` with ball growth `V`;
the constants do not depend on `Λ`.

Ported from LionSR/QICLean commit 5f76b263e3a1c418645102d90f7bef6b92f04cf3,
\`QICLean/Analysis/RootChannel.lean\` (kernel lemmas only), as used by LionSR/TNLean commit
fc565830cec69e8226e521d56c86d39845d45576. Adapted to Lean/Mathlib 4.33.
-/

namespace AreaLaw

open Arealaw Matrix Finset MeasureTheory
open OpenAI (condExpect IsSupportedOn HasGlobalGap)
open Quasilocal (M)
open scoped Kronecker MatrixOrder ComplexOrder Matrix.Norms.L2Operator

/-! ## Absolute values -/

section Abs

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

omit [DecidableEq n] in
/-- D4.10.2. If `0 ≤ Y` and `Y² v = c² v` with `c ≥ 0`, then `Y v = c v`. -/
theorem mulVec_eq_smul_of_mul_self_mulVec {Y : Matrix n n ℂ} (hY : 0 ≤ Y) {c : ℝ}
    (hc : 0 ≤ c) {v : n → ℂ} (h : (Y * Y) *ᵥ v = ((c ^ 2 : ℝ) : ℂ) • v) :
    Y *ᵥ v = (c : ℂ) • v := by
  have hYpsd : Y.PosSemidef := nonneg_iff_posSemidef.mp hY
  set w := Y *ᵥ v - (c : ℂ) • v with hw
  have hYw : Y *ᵥ w = -(c : ℂ) • w := by
    rw [hw, mulVec_sub, mulVec_mulVec, h, mulVec_smul, smul_sub, neg_smul, neg_smul,
      smul_smul]
    push_cast
    rw [sq]; abel
  have hnn : 0 ≤ star w ⬝ᵥ (Y *ᵥ w) := hYpsd.dotProduct_mulVec_nonneg w
  rw [hYw, dotProduct_smul] at hnn
  rcases hc.lt_or_eq with hcpos | hc0
  · have hcC : (0 : ℂ) < c := by exact_mod_cast hcpos
    have hprod : (c : ℂ) * (star w ⬝ᵥ w) = 0 := by
      refine le_antisymm ?_ (mul_nonneg hcC.le (dotProduct_star_self_nonneg w))
      rwa [smul_eq_mul, neg_mul, neg_nonneg] at hnn
    have : w = 0 :=
      dotProduct_star_self_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hcC.ne')
    rwa [hw, sub_eq_zero] at this
  · subst hc0
    simp only [Complex.ofReal_zero, zero_smul]
    have h0 : (Y * Y) *ᵥ v = 0 := by simpa using h
    have : star (Y *ᵥ v) ⬝ᵥ (Y *ᵥ v) = 0 := by
      rw [star_mulVec, ← dotProduct_mulVec, hYpsd.isHermitian.eq, mulVec_mulVec, h0,
        dotProduct_zero]
    exact dotProduct_star_self_eq_zero.mp this

set_option linter.unusedDecidableInType false in
/-- D4.10.7. Square roots commute with tensoring by an identity: `√M ⊗ I = √(M ⊗ I)`. -/
theorem sqrt_kronecker_one {κ : Type*} [Fintype κ] [DecidableEq κ] {M : Matrix n n ℂ}
    (hM : 0 ≤ M) :
    CFC.sqrt M ⊗ₖ (1 : Matrix κ κ ℂ) = CFC.sqrt (M ⊗ₖ (1 : Matrix κ κ ℂ)) := by
  have hpos : ∀ X : Matrix n n ℂ, 0 ≤ X → 0 ≤ X ⊗ₖ (1 : Matrix κ κ ℂ) := fun X hX =>
    ((nonneg_iff_posSemidef.mp hX).kronecker PosSemidef.one).nonneg
  refine ((CFC.sqrt_eq_iff _ _ (hpos M hM) (hpos _ (CFC.sqrt_nonneg M))).mpr ?_).symm
  rw [← mul_kronecker_mul, Matrix.mul_one, CFC.sqrt_mul_sqrt_self M hM]

set_option linter.unusedDecidableInType false in
theorem sqrt_submatrix {N : Matrix n n ℂ} (hN : 0 ≤ N) (e : m ≃ n) :
    CFC.sqrt (N.submatrix e e) = (CFC.sqrt N).submatrix e e := by
  have hpos : ∀ X : Matrix n n ℂ, 0 ≤ X → 0 ≤ X.submatrix e e := fun X hX =>
    ((nonneg_iff_posSemidef.mp hX).submatrix e).nonneg
  refine (CFC.sqrt_eq_iff _ _ (hpos N hN) (hpos _ (CFC.sqrt_nonneg N))).mpr ?_
  rw [submatrix_mul_equiv, CFC.sqrt_mul_sqrt_self N hN]

/-- D4.6.7. `|Z ⊗ I_Y| = |Z| ⊗ I_Y`. -/
theorem abs_extendId {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
    [∀ i, DecidableEq (loc i)] {S T : Finset σ} (h : S ⊆ T)
    (Z : Matrix (Reg loc S) (Reg loc S) ℂ) :
    CFC.abs (extendId h Z) = extendId h (CFC.abs Z) := by
  have hZ : 0 ≤ star Z * Z := star_mul_self_nonneg Z
  rw [extendId_eq_kronecker, extendId_eq_kronecker, CFC.abs, CFC.abs, star_eq_conjTranspose,
    conjTranspose_submatrix, submatrix_mul_equiv, conjTranspose_kronecker, conjTranspose_one,
    ← mul_kronecker_mul, Matrix.mul_one, ← star_eq_conjTranspose,
    sqrt_submatrix (((nonneg_iff_posSemidef.mp hZ).kronecker PosSemidef.one).nonneg),
    ← sqrt_kronecker_one hZ]

theorem IsSupportedOn.abs {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
    [∀ i, DecidableEq (loc i)] {S T : Finset σ} {h : S ⊆ T}
    {B : Matrix (Reg loc T) (Reg loc T) ℂ} (hB : IsSupportedOn h B) :
    IsSupportedOn h (CFC.abs B) := by
  obtain ⟨Z, rfl⟩ := hB
  exact ⟨CFC.abs Z, abs_extendId h Z⟩

/-- D4.6.6 (D4.9 with `U = M²`, `V = M'²`). For Hermitian `M, M'`,
`‖|M| - |M'|‖ ≤ ((‖M‖ + ‖M'‖) ‖M - M'‖)^{1/2}`. -/
theorem norm_abs_sub_abs_le {M M' : Matrix n n ℂ} (hM : M.IsHermitian) (hM' : M'.IsHermitian) :
    ‖CFC.abs M - CFC.abs M'‖ ≤ Real.sqrt ((‖M‖ + ‖M'‖) * ‖M - M'‖) := by
  refine (CFC.norm_sqrt_sub_sqrt_le (star_mul_self_nonneg M) (star_mul_self_nonneg M')).trans
    (Real.sqrt_le_sqrt ?_)
  rw [star_eq_conjTranspose, star_eq_conjTranspose, hM.eq, hM'.eq,
    show M * M - M' * M' = M * (M - M') + (M - M') * M' by noncomm_ring]
  calc _ ≤ ‖M‖ * ‖M - M'‖ + ‖M - M'‖ * ‖M'‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ = _ := by ring

end Abs

/-! ## D4.6.9: the component of the anchor -/

namespace GraphDomain

variable {σ : Type*} [DecidableEq σ] (G : SimpleGraph σ) {loc : σ → Type*}
  [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)]

/-- Inside a finite `Λ` a finite distance is less than `|Λ|`. -/
theorem domainEDist_lt_card {Λ : Finset σ} {x y : σ} (h : domainEDist G Λ x y ≠ ⊤) :
    domainEDist G Λ x y < #Λ := by
  unfold domainEDist at h ⊢
  split_ifs at h ⊢ with hxy
  · obtain ⟨p⟩ := SimpleGraph.edist_ne_top_iff_reachable.1 h
    have hlt : (p.toPath).1.length < #Λ := by simpa using (p.toPath).2.length_lt
    exact (SimpleGraph.edist_le (p.toPath).1).trans_lt (by exact_mod_cast hlt)
  · exact absurd rfl h

/-- For `l ≥ |Λ|` the ball `N_l(a)` is the component of `a`. -/
theorem graphNbhd_eq_component {Λ : Finset σ} {a : σ} {l : ℕ} (hl : #Λ ≤ l) :
    graphNbhd G Λ {a} l = component G Λ a := by
  ext x
  simp only [graphNbhd, component, Finset.mem_filter, Finset.mem_singleton, iInf_iInf_eq_left]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
  · rw [domainEDist_comm]
    exact ne_top_of_le_ne_top (ENat.natCast_ne_top l) h
  · rw [domainEDist_comm] at h
    exact (domainEDist_lt_card G h).le.trans (by exact_mod_cast hl)

/-- D4.6.9. An operator whose tail `‖k - E_{a,l} k‖` tends to `0` is supported in the
component of `a`. -/
theorem isSupportedOn_component_of_tail {Λ : Finset σ} {a : σ}
    {k : Matrix (Reg loc Λ) (Reg loc Λ) ℂ} {C c α : ℝ} (hc : 0 < c) (hα : 0 < α)
    (htail : ∀ l : ℕ, ‖k - E G Λ a l k‖ ≤ C * Real.exp (-c * (l : ℝ) ^ α)) :
    IsSupportedOn (component_subset G Λ a) k := by
  set K := condExpect (component_subset G Λ a) k
  have hE : ∀ l : ℕ, #Λ ≤ l → E G Λ a l k = K := fun l hl => by
    have := graphNbhd_eq_component G (a := a) hl
    unfold E
    congr 1
  have hlim : Filter.Tendsto (fun l : ℕ => C * Real.exp (-c * (l : ℝ) ^ α)) Filter.atTop
      (nhds 0) := by
    have h1 : Filter.Tendsto (fun l : ℕ => c * (l : ℝ) ^ α) Filter.atTop Filter.atTop :=
      ((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop).const_mul_atTop hc
    simpa [neg_mul] using (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul C
  have hle : ‖k - K‖ ≤ 0 := ge_of_tendsto hlim
    (Filter.eventually_atTop.2 ⟨#Λ, fun l hl => hE l hl ▸ htail l⟩)
  have hkK : k = K := sub_eq_zero.1 (norm_le_zero_iff.1 hle)
  rw [hkK]
  exact ⟨_, (extendId_smul _ _ _).symm⟩

end GraphDomain

/-! ## D4.6 Proposition 4.3 -/

section Prop43

open GraphDomain

theorem smul_le_smul_of_le {n : Type*} {A B : Matrix n n ℂ}
    (h : A ≤ B) {c : ℂ} (hc : 0 ≤ c) : c • A ≤ c • B := by
  rw [Matrix.le_iff] at h ⊢
  rw [← smul_sub]
  exact h.smul hc

variable {σ : Type*} [DecidableEq σ] (G : SimpleGraph σ) (V : ℕ → ℕ)
  (hV : ∀ (Λ : Finset σ) (x : σ) (r : ℕ), #(ball G Λ x r) ≤ V r)
  {loc : σ → Type} [∀ i, Fintype (loc i)] [∀ i, DecidableEq (loc i)] [∀ i, Nonempty (loc i)]

omit [∀ i, Nonempty (loc i)] in
theorem isHermitian_E {Λ : Finset σ} {a : σ} {l : ℕ} {B : Matrix (Reg loc Λ) (Reg loc Λ) ℂ}
    (hB : B.IsHermitian) : (E G Λ a l B).IsHermitian := by
  unfold E condExpect
  rw [IsHermitian, conjTranspose_smul, (isHermitian_extendId _ (isHermitian_ptrace _ hB)).eq]
  congr 1
  simp

include hV in
/-- D4.6 (Proposition 4.3). Suppose `HΩ = E₀Ω`, `‖Ω‖ = 1`, `H - E₀I ≥ Δ(I - P_Ω)`. For each
integer `p ≥ 1`, `α = p/(p+1)`, there are operators `k_i` (`i ∈ 𝓘`, anchors retained) and
`c_* > 0` with `0 ≤ k_i ≤ I`, `k_i Ω = 0`, `H_F := ∑_i k_i ≥ c_*⁻¹(H - E₀I) ≥ g(I - P_Ω)`,
`g := Δ/c_*`. Furthermore `k_{i,l} := E_{i,l}(k_i) ∈ [0, I]`,
`‖k_i - k_{i,l}‖ ≤ C e^{-c l^α}` (`l ∈ ℤ_{≥0}`). Each `k_i` is supported in the connected
component of `a_i`. `c_*, g` depend on `p` (not on `|Λ|`); `C, c` on `p, R, J, Δ` (and the
ball growth `V`). -/
theorem prop_4_3 {p : ℕ} (hp : 1 ≤ p) (R : ℕ) (J Δ : ℝ) (hΔ : 0 < Δ) :
    ∃ cstar : ℝ, 0 < cstar ∧ ∃ C c : ℝ, 0 < c ∧
    ∀ Λ : Finset σ, ∀ Φ : (X : Finset σ) → Matrix (Reg loc X) (Reg loc X) ℂ,
      IsAdmissible G Λ R J Φ →
    ∀ (Ω : Reg loc Λ → ℂ) (_ : star Ω ⬝ᵥ Ω = 1) (E₀ : ℝ),
      hamiltonian Λ Φ *ᵥ Ω = (E₀ : ℂ) • Ω → HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ →
    ∀ anchor : Finset σ → σ, (∀ X ∈ supports G Λ R, anchor X ∈ X) →
    ∃ k : Finset σ → Matrix (Reg loc Λ) (Reg loc Λ) ℂ,
      (∀ X ∈ supports G Λ R, 0 ≤ k X ∧ k X ≤ 1 ∧ k X *ᵥ Ω = 0) ∧
      (cstar : ℂ)⁻¹ • (hamiltonian Λ Φ - (E₀ : ℂ) • 1) ≤ ∑ X ∈ supports G Λ R, k X ∧
      ((Δ / cstar : ℝ) : ℂ) • (1 - vecMulVec Ω (star Ω)) ≤
        (cstar : ℂ)⁻¹ • (hamiltonian Λ Φ - (E₀ : ℂ) • 1) ∧
      (∀ X ∈ supports G Λ R, ∀ l : ℕ,
        0 ≤ E G Λ (anchor X) l (k X) ∧ E G Λ (anchor X) l (k X) ≤ 1 ∧
        ‖k X - E G Λ (anchor X) l (k X)‖ ≤ C * Real.exp (-c * (l : ℝ) ^ ((p : ℝ) / (p + 1)))) ∧
      ∀ X ∈ supports G Λ R, IsSupportedOn (component_subset G Λ (anchor X)) (k X) := by
  set δ : ℝ := Δ / 2
  have hδ : 0 < δ := half_pos hΔ
  obtain ⟨-, -, -, -, -, -, -, hinv, -, hfi, hf1⟩ := lemma_4_2 p hp δ hδ
  have hχ0 : ∀ ω : ℝ, δ ≤ |ω| → ∫ t, (f p δ t : ℂ) * Complex.exp (t * ω * Complex.I) = 0 := by
    intro ω hω
    rw [← hinv ω]
    simp [χ, not_lt.2 hω]
  set α : ℝ := (p : ℝ) / (p + 1)
  have hα : 0 < α := by have : (0 : ℝ) < p := by exact_mod_cast hp
                        positivity
  -- D4.6.2: `c_* = max {1, J(‖f‖₁ + 1)}`
  set L1 := ∫ t, |f p δ t|
  set cstar : ℝ := max 1 (J * (L1 + 1))
  have hcs : 0 < cstar := lt_of_lt_of_le one_pos (le_max_left _ _)
  -- D4.8 at the rate `c = 1` of D4.4
  obtain ⟨C', c'', hC', hc'', hloc⟩ := step_4_8 G V hV (loc := loc) hp hδ R J one_pos
  refine ⟨cstar, hcs, cstar⁻¹ * 2 * Real.sqrt (2 * cstar * C' * J), c'' / 2, by positivity, ?_⟩
  intro Λ Φ hΦ Ω hΩ E₀ hHΩ hgap anchor hanchor
  set H := hamiltonian Λ Φ
  let h : Finset σ → Matrix (Reg loc Λ) (Reg loc Λ) ℂ := fun X =>
    if hX : X ⊆ Λ then extendId hX (Φ X) else 0
  have hh_eq : ∀ X (hX : X ∈ supports G Λ R),
      h X = extendId ((GraphDomain.mem_supports G).1 hX).1 (Φ X) := fun X hX =>
    dif_pos ((GraphDomain.mem_supports G).1 hX).1
  have hherm : ∀ X ∈ supports G Λ R, (h X).IsHermitian := fun X hX => by
    rw [hh_eq X hX]
    exact isHermitian_extendId _ (hΦ X ((GraphDomain.mem_supports G).1 hX).1).1
  have hJ : ∀ X ∈ supports G Λ R, ‖h X‖ ≤ J := fun X hX => by
    rw [hh_eq X hX]
    exact (norm_extendId_le _ _).trans (hΦ X ((GraphDomain.mem_supports G).1 hX).1).2.1
  have hHsum : H = ∑ X ∈ supports G Λ R, h X := by
    change hamiltonian Λ Φ = _
    rw [hamiltonian_eq_sum_supports G hΦ, ← Finset.sum_coe_sort (supports G Λ R) h]
    exact Finset.sum_congr rfl fun X _ => (hh_eq X.1 X.2).symm
  -- D4.6.1 = D4.7
  obtain ⟨-, hMherm, hMΩ, hMsum, hMnorm⟩ := step_4_7 (supports G Λ R) h hherm hJ hHsum hΩ hHΩ
    hgap hΔ (half_le_self hΔ.le) hfi hf1 hχ0
  set Mi : Finset σ → Matrix (Reg loc Λ) (Reg loc Λ) ℂ := fun X => M H Ω (f p δ) (h X)
  have hcsC : (0 : ℂ) ≤ (cstar : ℂ)⁻¹ := by
    rw [← Complex.ofReal_inv]; exact_mod_cast (inv_pos.2 hcs).le
  have hnorm_smul : ∀ B : Matrix (Reg loc Λ) (Reg loc Λ) ℂ, ‖(cstar : ℂ)⁻¹ • B‖ = cstar⁻¹ * ‖B‖ :=
    fun B => by rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hcs.le]
  refine ⟨fun X => (cstar : ℂ)⁻¹ • CFC.abs (Mi X), ?_⟩
  -- D4.6.2
  have hk0 : ∀ X, 0 ≤ (cstar : ℂ)⁻¹ • CFC.abs (Mi X) := fun X =>
    nonneg_iff_posSemidef.2 ((nonneg_iff_posSemidef.1 (CFC.abs_nonneg _)).smul hcsC)
  have hk1 : ∀ X ∈ supports G Λ R, (cstar : ℂ)⁻¹ • CFC.abs (Mi X) ≤ 1 := fun X hX => by
    refine (CStarAlgebra.norm_le_one_iff_of_nonneg _ (hk0 X)).1 ?_
    rw [hnorm_smul, CFC.norm_abs, inv_mul_le_one₀ hcs]
    exact (hMnorm X hX).trans (le_max_right _ _)
  -- D4.6.6–7: the tail
  have htail : ∀ X ∈ supports G Λ R, ∀ l : ℕ,
      ‖(cstar : ℂ)⁻¹ • CFC.abs (Mi X) - E G Λ (anchor X) l ((cstar : ℂ)⁻¹ • CFC.abs (Mi X))‖ ≤
        cstar⁻¹ * 2 * Real.sqrt (2 * cstar * C' * J) * Real.exp (-(c'' / 2) * (l : ℝ) ^ α) := by
    intro X hX l
    set a := anchor X
    set EM := E G Λ a l (Mi X)
    have hEM : EM.IsHermitian := isHermitian_E G (hMherm X hX)
    have hfix : E G Λ a l (CFC.abs EM) = CFC.abs EM :=
      (eq_quasilocal_ce Λ a l).2.2.2 _ (IsSupportedOn.abs (isSupportedOn_E (G := G) Λ a l (Mi X)))
    have hloc' : ‖Mi X - EM‖ ≤ C' * Real.exp (-(c'' * (l : ℝ) ^ α)) * J := by
      have := hloc hΦ hX (hanchor X hX) Ω l
      rw [← hh_eq X hX] at this
      exact this.trans (mul_le_mul_of_nonneg_left (hJ X hX) (by positivity))
    have hJ0 : 0 ≤ J := (norm_nonneg _).trans (hJ X hX)
    have hMc : ‖Mi X‖ ≤ cstar := (hMnorm X hX).trans (le_max_right _ _)
    have hEMc : ‖EM‖ ≤ cstar := (norm_E_le _ _ _ _).trans hMc
    -- D4.6.7
    have h7 : ‖CFC.abs (Mi X) - E G Λ a l (CFC.abs (Mi X))‖ ≤
        2 * ‖CFC.abs (Mi X) - CFC.abs EM‖ := by
      have hdec : CFC.abs (Mi X) - E G Λ a l (CFC.abs (Mi X)) =
          (CFC.abs (Mi X) - CFC.abs EM) + E G Λ a l (CFC.abs EM - CFC.abs (Mi X)) := by
        rw [E_sub, hfix]; abel
      rw [hdec]
      calc _ ≤ ‖CFC.abs (Mi X) - CFC.abs EM‖ + ‖CFC.abs EM - CFC.abs (Mi X)‖ :=
            (norm_add_le _ _).trans (add_le_add le_rfl (norm_E_le _ _ _ _))
        _ = _ := by rw [norm_sub_rev (CFC.abs EM)]; ring
    -- D4.6.6
    set e := Real.exp (-(c'' * (l : ℝ) ^ α))
    have h6 : ‖CFC.abs (Mi X) - CFC.abs EM‖ ≤
        Real.sqrt (2 * cstar * C' * J) * Real.exp (-(c'' / 2) * (l : ℝ) ^ α) := by
      have hee : Real.exp (-(c'' / 2) * (l : ℝ) ^ α) = Real.sqrt e := by
        rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le,
          ← Real.exp_add]
        ring_nf
      rw [hee, ← Real.sqrt_mul (by positivity)]
      refine (norm_abs_sub_abs_le (hMherm X hX) hEM).trans (Real.sqrt_le_sqrt ?_)
      calc (‖Mi X‖ + ‖EM‖) * ‖Mi X - EM‖ ≤ (2 * cstar) * (C' * e * J) :=
            mul_le_mul (by linarith) hloc' (norm_nonneg _) (by positivity)
        _ = 2 * cstar * C' * J * e := by ring
    have hEk : E G Λ a l ((cstar : ℂ)⁻¹ • CFC.abs (Mi X)) =
        (cstar : ℂ)⁻¹ • E G Λ a l (CFC.abs (Mi X)) := (Eₗ G Λ a l).map_smul _ _
    rw [hEk, ← smul_sub, hnorm_smul]
    calc cstar⁻¹ * ‖CFC.abs (Mi X) - E G Λ a l (CFC.abs (Mi X))‖
        ≤ cstar⁻¹ * (2 * (Real.sqrt (2 * cstar * C' * J) *
            Real.exp (-(c'' / 2) * (l : ℝ) ^ α))) := by
          gcongr
          exact h7.trans (by gcongr)
      _ = _ := by ring
  refine ⟨fun X hX => ⟨hk0 X, hk1 X hX, ?_⟩, ?_, ?_, fun X hX l => ?_, fun X hX => ?_⟩
  · -- D4.6.3: `ker |M_i| = ker M_i`
    rw [Matrix.smul_mulVec]
    have h0 : (CFC.abs (Mi X) * CFC.abs (Mi X)) *ᵥ Ω = (((0 : ℝ) ^ 2 : ℝ) : ℂ) • Ω := by
      rw [CFC.abs_mul_abs, ← mulVec_mulVec, hMΩ X hX, mulVec_zero]
      simp
    have h1 := mulVec_eq_smul_of_mul_self_mulVec (Y := CFC.abs (Mi X)) (CFC.abs_nonneg (Mi X))
      (c := 0) le_rfl (v := Ω) h0
    rw [h1, Complex.ofReal_zero, zero_smul, smul_zero]
  · -- D4.6.4: `|M_i| ≥ M_i`
    rw [← hMsum, Finset.smul_sum]
    refine Finset.sum_le_sum fun X hX => smul_le_smul_of_le ?_ hcsC
    have hsa : IsSelfAdjoint (Mi X) := hMherm X hX
    have := CFC.abs_sub_self (Mi X) hsa
    rw [← sub_nonneg, this]
    exact nsmul_nonneg (CFC.negPart_nonneg _) 2
  · -- D4.6.4: `c_*⁻¹ (H - E₀ I) ≥ g (I - P_Ω)`
    rw [show ((Δ / cstar : ℝ) : ℂ) • (1 - vecMulVec Ω (star Ω)) =
        (cstar : ℂ)⁻¹ • ((Δ : ℂ) • (1 - vecMulVec Ω (star Ω))) by
      rw [smul_smul]; congr 1; push_cast; ring]
    exact smul_le_smul_of_le hgap hcsC
  · -- D4.6.8
    obtain ⟨h0, h1⟩ := (eq_quasilocal_ce Λ (anchor X) l).2.2.1 _ (hk0 X) (hk1 X hX)
    exact ⟨h0, h1, htail X hX l⟩
  · -- D4.6.9
    exact isSupportedOn_component_of_tail G (by positivity) hα (htail X hX)

end Prop43

/-- D4.6 on the square lattice over `ℂ`: the frozen `PositiveReplacement` is the
`G = squareLattice`, `V = v 2` instance of `prop_4_3`. -/
theorem positiveReplacement_complex (q R : ℕ) (J Δ : ℝ) (p : ℕ) (hq : 1 ≤ q) (hΔ : 0 < Δ)
    (hp : 1 ≤ p) : OpenAI.PositiveReplacement ℂ q R J Δ p := by
  have : ∀ i, Nonempty (OpenAI.Qudits q i) := fun _ => ⟨⟨0, hq⟩⟩
  obtain ⟨cs, hcs, C, c, hc, hP⟩ := prop_4_3 squareLattice (v 2) eq_ball_count_two
    (loc := OpenAI.Qudits q) hp R J Δ hΔ
  refine ⟨cs, hcs, C, c, hc, fun Λ Φ hΦ Ω hΩ E₀ hHΩ hgap anchor hanchor => ?_⟩
  obtain ⟨k, h1, h2, h3, h4, h5⟩ := hP Λ Φ hΦ Ω hΩ E₀ hHΩ hgap anchor hanchor
  exact ⟨k, h1, h2, h3, h4, h5⟩

end AreaLaw
