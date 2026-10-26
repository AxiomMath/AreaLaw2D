import AreaLaw.S08_Comparators.Interfaces
import AreaLawForMathlib.RepresentationTheory.SchurWeyl.ProductVectorMarginal
import AreaLawForMathlib.QuantumInfo.Entropy.Concavity
import AreaLawForMathlib.Analysis.Matrix.SpectralVectorJensen
import AreaLawForMathlib.Analysis.Matrix.CommutingProjectionProduct
import AreaLawForMathlib.RepresentationTheory.SchurWeyl.LabelObservableCalculus
import AreaLawForMathlib.Analysis.Matrix.ProjectionVectorEstimates

/-!
# §8.3 Upper comparisons: post marginals and the rough upper bound (D8.17–D8.20)

Digest `digest/08-comparators.md` D8.17–D8.20, paper `paper/sections/07-comparators.tex`
322–381. No geometry: arbitrary finite site type and local dimensions. The `B`-marginal of one
copy of `post_k` is `ρ_{ψ,B}` (a matrix on `𝓗_B = Reg (Fin ∘ n) B`); expectations of label
functions of `B` in `post_k` are traces against `ρ_{ψ,B}^{⊗k}` (`step_8_17`).
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Filter Topology Arealaw Entropy PermutationRepresentation

namespace AreaLaw.Comparators

universe u v

/-! ## Moments of a fixed finite density -/

section FixedMoments

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- A fixed finite density has marginal moment data (D8.5) with `C₀ = c₀ = 1`:
`log Tr ρ^{1-u} ≤ u S(ρ) + 𝓑 u²` for `|u| ≤ 𝓑^{-1/2}`. -/
theorem exists_mgf_bound {ρ : Matrix Ω Ω ℂ} (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    ∃ 𝓑 : ℝ, 1 ≤ 𝓑 ∧ ∀ u : ℝ, |u| ≤ 1 / Real.sqrt 𝓑 →
      Real.log (trPowPos ρ hρ.isHermitian u) ≤ u * vonNeumann hρ.isHermitian + 1 * 𝓑 * u ^ 2 := by
  set ev := hρ.isHermitian.eigenvalues
  have hev0 : ∀ i, 0 ≤ ev i := hρ.eigenvalues_nonneg
  have hsum : ∑ i, ev i = 1 := by
    have h := hρ.isHermitian.trace_eq_sum_eigenvalues
    rw [htr] at h
    have := congrArg Complex.re h
    simpa [ev] using this.symm
  have hev1 : ∀ i, ev i ≤ 1 := fun i => hsum ▸
    Finset.single_le_sum (fun j _ => hev0 j) (Finset.mem_univ i)
  set ℓ : Ω → ℝ := fun i => -Real.log (ev i)
  have hℓ0 : ∀ i, 0 ≤ ℓ i := fun i => neg_nonneg.mpr (Real.log_nonpos (hev0 i) (hev1 i))
  set L := ∑ i, ℓ i
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun i _ => hℓ0 i
  have hℓL : ∀ i, ℓ i ≤ L := fun i => Finset.single_le_sum (fun j _ => hℓ0 j) (Finset.mem_univ i)
  refine ⟨(1 + L) ^ 2, by nlinarith, fun u hu => ?_⟩
  rw [Real.sqrt_sq (by linarith)] at hu
  have huℓ : ∀ i, |u * ℓ i| ≤ 1 := fun i => by
    rw [abs_mul, abs_of_nonneg (hℓ0 i)]
    calc |u| * ℓ i ≤ 1 / (1 + L) * (1 + L) :=
          mul_le_mul hu (by linarith [hℓL i]) (hℓ0 i) (by positivity)
      _ = 1 := by field_simp
  have hterm : ∀ i, (if 0 < ev i then ev i ^ (1 - u) else 0) ≤
      ev i * (1 + u * ℓ i + (u * ℓ i) ^ 2) := fun i => by
    split_ifs with hi
    · rw [Real.rpow_def_of_pos hi]
      have h1 := Real.abs_exp_sub_one_sub_id_le (huℓ i)
      have h2 : Real.exp (Real.log (ev i) * (1 - u)) = ev i * Real.exp (u * ℓ i) := by
        rw [show Real.log (ev i) * (1 - u) = Real.log (ev i) + u * ℓ i by simp [ℓ]; ring,
          Real.exp_add, Real.exp_log hi]
      rw [h2]
      exact mul_le_mul_of_nonneg_left (by linarith [(abs_le.mp h1).2]) (hev0 i)
    · have : ev i = 0 := le_antisymm (not_lt.mp hi) (hev0 i)
      rw [this]; simp
  have hpos : 0 < trPowPos ρ hρ.isHermitian u := by
    obtain ⟨i, hi⟩ : ∃ i, 0 < ev i := by
      by_contra h
      push Not at h
      have : ∑ i, ev i = 0 := Finset.sum_eq_zero fun i _ => le_antisymm (h i) (hev0 i)
      linarith
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun i =>
      if 0 < ev i then ev i ^ (1 - u) else 0) (fun j _ => by
        split_ifs <;> [exact Real.rpow_nonneg (hev0 j) _; exact le_rfl]) (Finset.mem_univ i))
    simp only [hi, if_true]
    exact Real.rpow_pos_of_pos hi _
  have hS : vonNeumann hρ.isHermitian = ∑ i, ev i * ℓ i := by
    rw [vonNeumann_eq_H, H]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Real.negMulLog, ℓ, ev]
  have hsq : ∑ i, ev i * ℓ i ^ 2 ≤ (1 + L) ^ 2 := by
    calc ∑ i, ev i * ℓ i ^ 2 ≤ ∑ i, ev i * L ^ 2 :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (hℓ0 i) (hℓL i) 2) (hev0 i)
      _ = L ^ 2 := by rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ (1 + L) ^ 2 := pow_le_pow_left₀ hL0 (by linarith) 2
  have htp : trPowPos ρ hρ.isHermitian u ≤ 1 + u * vonNeumann hρ.isHermitian +
      u ^ 2 * ∑ i, ev i * ℓ i ^ 2 := by
    calc trPowPos ρ hρ.isHermitian u ≤ ∑ i, ev i * (1 + u * ℓ i + (u * ℓ i) ^ 2) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = _ := by
          rw [hS, Finset.mul_sum, Finset.mul_sum]
          simp only [mul_add, mul_one, Finset.sum_add_distrib, hsum]
          congr 1
          · congr 1
            exact Finset.sum_congr rfl fun i _ => by ring
          · exact Finset.sum_congr rfl fun i _ => by ring
  have := Real.log_le_sub_one_of_pos hpos
  nlinarith [sq_nonneg u]

end FixedMoments

/-! ## Physical regions of `𝒱` -/

section Regions

variable {σ : Type u} [DecidableEq σ] {n : σ → ℕ}

omit [DecidableEq σ] in
theorem Upper.phys_mem_physReg {B : Finset σ} {v : σ} : Site.phys v ∈ physReg B ↔ v ∈ B := by
  unfold physReg
  exact Finset.mem_map' _

omit [DecidableEq σ] in
theorem Upper.C_not_mem_physReg (B : Finset σ) : Site.C ∉ physReg B := by simp [physReg]

omit [DecidableEq σ] in
theorem Upper.R_not_mem_physReg (B : Finset σ) : Site.R ∉ physReg B := by simp [physReg]

/-- `𝓗_B` as the tensor factors `physReg B` of `𝒱`. -/
def regPhys (d : ℕ) (B : Finset σ) :
    Reg (fun v => Fin (n v)) B ≃
      TensorPower.SubConfig (fun f => Fin (dims n d f)) (physReg B) where
  toFun a f := match f with
    | ⟨.phys v, h⟩ => a ⟨v, Upper.phys_mem_physReg.mp h⟩
    | ⟨.C, h⟩ => absurd h (Upper.C_not_mem_physReg B)
    | ⟨.R, h⟩ => absurd h (Upper.R_not_mem_physReg B)
  invFun x v := x ⟨.phys v.1, Upper.phys_mem_physReg.mpr v.2⟩
  left_inv a := rfl
  right_inv x := by
    funext ⟨f, h⟩
    rcases f with v | _ | _
    · rfl
    · exact absurd h (Upper.C_not_mem_physReg B)
    · exact absurd h (Upper.R_not_mem_physReg B)

/-- The complement of `physReg B` in `𝒱`: the physical complement of `B`, `C` and `R`. -/
def complPhys (d : ℕ) (B : Finset σ) :
    TensorPower.ComplConfig (fun f => Fin (dims n d f)) (physReg B) ≃
      TensorPower.ComplConfig (fun v => Fin (n v)) B × Fin d × Fin d where
  toFun b := (fun v => b ⟨.phys v.1, fun h => v.2 (Upper.phys_mem_physReg.mp h)⟩,
    b ⟨.C, Upper.C_not_mem_physReg B⟩, b ⟨.R, Upper.R_not_mem_physReg B⟩)
  invFun q f := match f with
    | ⟨.phys v, h⟩ => q.1 ⟨v, fun h' => h (Upper.phys_mem_physReg.mpr h')⟩
    | ⟨.C, _⟩ => q.2.1
    | ⟨.R, _⟩ => q.2.2
  left_inv b := by
    funext ⟨f, h⟩
    rcases f with v | _ | _ <;> rfl
  right_inv q := rfl

/-- A configuration of `𝒱` glued from `physReg B` and its complement. -/
abbrev joinPhys (d : ℕ) (B : Finset σ) (a : Reg (fun v => Fin (n v)) B)
    (q : TensorPower.ComplConfig (fun v => Fin (n v)) B × Fin d × Fin d) :
    SiteConfig (dims n d) :=
  (Equiv.piEquivPiSubtypeProd (· ∈ physReg B) (fun f => Fin (dims n d f))).symm
    (regPhys d B a, (complPhys d B).symm q)

/-- A physical configuration glued from `B` and its complement. -/
abbrev join (B : Finset σ) (a : Reg (fun v => Fin (n v)) B)
    (b : TensorPower.ComplConfig (fun v => Fin (n v)) B) : SiteConfig n :=
  (Equiv.piEquivPiSubtypeProd (· ∈ B) (fun v => Fin (n v))).symm (a, b)

theorem physPart_joinPhys (d : ℕ) (B : Finset σ) (a : Reg (fun v => Fin (n v)) B)
    (q : TensorPower.ComplConfig (fun v => Fin (n v)) B × Fin d × Fin d) :
    physPart (joinPhys d B a q) = join B a q.1 := by
  funext v
  simp only [physPart, joinPhys, join, Equiv.piEquivPiSubtypeProd_symm_apply]
  by_cases hv : v ∈ B
  · rw [dif_pos (Upper.phys_mem_physReg.mpr hv), dif_pos hv]; rfl
  · rw [dif_neg (fun h => hv (Upper.phys_mem_physReg.mp h)), dif_neg hv]; rfl

theorem joinPhys_C (d : ℕ) (B : Finset σ) (a : Reg (fun v => Fin (n v)) B)
    (q : TensorPower.ComplConfig (fun v => Fin (n v)) B × Fin d × Fin d) :
    joinPhys d B a q .C = q.2.1 := by
  simp only [joinPhys, Equiv.piEquivPiSubtypeProd_symm_apply]
  rw [dif_neg (Upper.C_not_mem_physReg B)]; rfl

theorem joinPhys_R (d : ℕ) (B : Finset σ) (a : Reg (fun v => Fin (n v)) B)
    (q : TensorPower.ComplConfig (fun v => Fin (n v)) B × Fin d × Fin d) :
    joinPhys d B a q .R = q.2.2 := by
  simp only [joinPhys, Equiv.piEquivPiSubtypeProd_symm_apply]
  rw [dif_neg (Upper.R_not_mem_physReg B)]; rfl

/-- `𝒱 = 𝓗_B ⊗ 𝓗_{B^c} ⊗ 𝓗_C ⊗ 𝓗_R` on configurations. -/
def splitPhys (d : ℕ) (B : Finset σ) :
    Reg (fun v => Fin (n v)) B × (TensorPower.ComplConfig (fun v => Fin (n v)) B × Fin d × Fin d) ≃
      SiteConfig (dims n d) :=
  (Equiv.prodCongr (regPhys d B) (complPhys d B).symm).trans
    (Equiv.piEquivPiSubtypeProd (· ∈ physReg B) (fun f => Fin (dims n d f))).symm

theorem joinPhys_phys (d : ℕ) (B : Finset σ) (a : Reg (fun v => Fin (n v)) B)
    (q : TensorPower.ComplConfig (fun v => Fin (n v)) B × Fin d × Fin d) {v : σ} (hv : v ∈ B) :
    joinPhys d B a q (.phys v) = a ⟨v, hv⟩ := by
  have := congrFun (physPart_joinPhys d B a q) v
  simp only [physPart] at this
  rw [this, join, Equiv.piEquivPiSubtypeProd_symm_apply, dif_pos hv]

variable {X B : Finset σ}

theorem restrictX_join (h : Disjoint X B) (a : Reg (fun v => Fin (n v)) B)
    (b : TensorPower.ComplConfig (fun v => Fin (n v)) B) :
    restrictX (X := X) (join B a b) = TensorPower.complRestr (fun v => Fin (n v)) h b := by
  funext v
  simp only [restrictX, join, Equiv.piEquivPiSubtypeProd_symm_apply, TensorPower.complRestr]
  rw [dif_neg (Finset.disjoint_left.mp h v.2)]

theorem join_complReplace (a : Reg (fun v => Fin (n v)) B)
    (b : TensorPower.ComplConfig (fun v => Fin (n v)) B) (y : Reg (fun v => Fin (n v)) X)
    (h : Disjoint X B) :
    join B a (TensorPower.complReplace (fun v => Fin (n v)) b y) = replaceX (join B a b) y := by
  funext v
  simp only [join, replaceX, Equiv.piEquivPiSubtypeProd_symm_apply, TensorPower.complReplace]
  by_cases hX : v ∈ X
  · rw [dif_neg (Finset.disjoint_left.mp h hX), dif_pos hX, dif_pos hX]
  · by_cases hB : v ∈ B <;> simp [hB, hX]

end Regions

/-! ## D8.17 Post marginals -/

section PostMarginal

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} {D : PhysData n} {X : Finset σ}

/-- One copy `B_{XC} ψ` of `post_k = B_{XC}^{⊗k} ⊗ ψ^{⊗k}`. -/
noncomputable def post₁ (E : TypicalSet D X) : SiteConfig (dims n E.d) → ℂ :=
  fun x => BXC E x * ψ E x

theorem post_eq_tensorVec (E : TypicalSet D X) (k : ℕ) :
    post E k = TensorPower.tensorVec k (post₁ E) := rfl

variable (D X) in
/-- `ω_{i,B} = Tr_rest |w_i⟩⟨w_i|` (normalized by `dim 𝓗_X`, as `w_i` is constant along `X`). -/
noncomputable def ω (i : Reg (fun v => Fin (n v)) X) (B : Finset σ) :
    Matrix (Reg (fun v => Fin (n v)) B) (Reg (fun v => Fin (n v)) B) ℂ :=
  ((dimReg n X : ℂ))⁻¹ • TensorPower.vecMarginal (fun v => Fin (n v)) (schmidtW (D := D) i) B

/-- `ρ_{ψ,B}`, the `B`-marginal of one copy `B_{XC} ψ` of `post_k`. -/
noncomputable def ρψ (E : TypicalSet D X) (B : Finset σ) :
    Matrix (Reg (fun v => Fin (n v)) B) (Reg (fun v => Fin (n v)) B) ℂ :=
  (TensorPower.vecMarginal (fun f => Fin (dims n E.d f)) (post₁ E) (physReg B)).submatrix
    (regPhys E.d B) (regPhys E.d B)

omit [Fintype σ] in
theorem dimReg_eq_card (X : Finset σ) :
    (dimReg n X : ℂ) = Fintype.card (Reg (fun v => Fin (n v)) X) := by
  simp [dimReg, Fintype.card_pi, Finset.prod_attach]

theorem ρ_eq_vecMarginal (B : Finset σ) :
    D.ρ B = TensorPower.vecMarginal (fun v => Fin (n v)) D.Ω B := by
  rw [PhysData.ρ, Replicas.marg_univ]
  rfl

/-- `∑_y ⟨y|i⟩ ⟨j|y⟩ = δ_{ij}` for the Schmidt vectors `|i⟩_X`. -/
theorem sum_schmidtX_mul_star (i j : Reg (fun v => Fin (n v)) X) :
    ∑ y, schmidtX (D := D) i y * star (schmidtX (D := D) j y) = if i = j then 1 else 0 := by
  have h := orthonormal_iff_ite.mp ((D.isHermitian_ρ X).eigenvectorBasis).orthonormal j i
  rw [PiLp.inner_apply] at h
  simp only [RCLike.inner_apply, schmidtX] at h ⊢
  calc _ = if j = i then 1 else 0 := h
    _ = _ := by by_cases hij : i = j <;> simp [hij, eq_comm]

/-- D8.17.1, the trace over `X`: orthonormal `|m⟩_X` kill the cross terms. -/
theorem sum_schmidtX_mul_schmidtW [∀ v, NeZero (n v)] (h11 : Step_8_11.{u}) {B : Finset σ}
    (hB : Disjoint B X) (m m' i j : Reg (fun v => Fin (n v)) X)
    (a a' : Reg (fun v => Fin (n v)) B) :
    ∑ b, (schmidtX (D := D) m (restrictX (join B a b)) *
        star (schmidtX (D := D) m' (restrictX (join B a' b)))) *
      (schmidtW (D := D) i (join B a b) * star (schmidtW (D := D) j (join B a' b))) =
    if m = m' then ((dimReg n X : ℂ))⁻¹ *
        ∑ b, schmidtW (D := D) i (join B a b) * star (schmidtW (D := D) j (join B a' b))
      else 0 := by
  have hN : (dimReg n X : ℂ) ≠ 0 := by
    rw [dimReg_eq_card]; exact_mod_cast Fintype.card_ne_zero
  have key := TensorPower.card_mul_sum_complRestr_mul (fun v => Fin (n v)) hB.symm
    (fun y => schmidtX (D := D) m y * star (schmidtX (D := D) m' y))
    (fun b => schmidtW (D := D) i (join B a b) * star (schmidtW (D := D) j (join B a' b)))
    (fun b y => by
      simp only [join_complReplace _ _ _ hB.symm, (h11 D X).2.1])
  rw [sum_schmidtX_mul_star, ← dimReg_eq_card] at key
  simp only [restrictX_join hB.symm]
  rw [← mul_right_inj' hN, key]
  split_ifs <;> simp [hN]

/-- D8.17.1 for `ρ_B`: tracing out `X` kills the cross terms, `ρ_B = ∑_i p_i ω_{i,B}`. -/
theorem ρ_eq_sum_ω [∀ v, NeZero (n v)] (h11 : Step_8_11.{u}) {B : Finset σ}
    (hB : Disjoint B X) : D.ρ B = ∑ i, (D.p X i : ℂ) • ω D X i B := by
  have hΩ := (h11 D X).1
  ext a a'
  rw [ρ_eq_vecMarginal, TensorPower.vecMarginal_apply]
  simp only [Matrix.sum_apply, Matrix.smul_apply, ω, smul_eq_mul, TensorPower.vecMarginal_apply,
    hΩ, star_sum, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => enter [2, b]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  have hj : ∀ j, ∑ b, (Real.sqrt (D.p X i) : ℂ) * schmidtX (D := D) i (restrictX (join B a b)) *
        schmidtW (D := D) i (join B a b) *
      star ((Real.sqrt (D.p X j) : ℂ) * schmidtX (D := D) j (restrictX (join B a' b)) *
        schmidtW (D := D) j (join B a' b)) =
      ((Real.sqrt (D.p X i) : ℂ) * star (Real.sqrt (D.p X j) : ℂ)) *
        (if i = j then ((dimReg n X : ℂ))⁻¹ *
          ∑ b, schmidtW (D := D) i (join B a b) * star (schmidtW (D := D) j (join B a' b))
          else 0) := fun j => by
    rw [← sum_schmidtX_mul_schmidtW h11 hB i j i j a a', Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [star_mul']
    ring
  simp only [hj, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hc : (Real.sqrt (D.p X i) : ℂ) * star (Real.sqrt (D.p X i) : ℂ) = D.p X i := by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt ((h11 D X).2.2.2.1 i)]
  rw [hc, Finset.mul_sum, Finset.mul_sum]

theorem TypicalSet.p_pos (E : TypicalSet D X) : ∀ i ∈ E.E, 0 < D.p X i :=
  fun i hi => (Real.exp_pos _).trans_le (E.lower i hi)

theorem TypicalSet.z_pos (E : TypicalSet D X) : 0 < E.z :=
  Finset.sum_pos E.p_pos E.nonempty

theorem TypicalSet.p'_nonneg (h11 : Step_8_11.{u}) (E : TypicalSet D X)
    (i : Reg (fun v => Fin (n v)) X) : 0 ≤ E.p' i :=
  div_nonneg ((h11 D X).2.2.2.1 i) E.z_pos.le

theorem ofReal_mul_star_ofReal_sqrt {r : ℝ} (hr : 0 ≤ r) :
    (Real.sqrt r : ℂ) * star (Real.sqrt r : ℂ) = r := by
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hr]

/-- D8.17.1 for `ρ_{ψ,B}`: tracing out `C`, `X` and `R` gives `ρ_{ψ,B} = ∑_{i ∈ E} p'_i ω_{i,B}`. -/
theorem ρψ_eq_sum_ω [∀ v, NeZero (n v)] (h11 : Step_8_11.{u}) {B : Finset σ}
    (hB : Disjoint B X) (E : TypicalSet D X) :
    ρψ E B = ∑ i ∈ E.E, (E.p' i : ℂ) • ω D X i B := by
  ext a a'
  simp only [ρψ, submatrix_apply, TensorPower.vecMarginal_apply, Matrix.sum_apply,
    Matrix.smul_apply, ω, smul_eq_mul]
  rw [← (complPhys E.d B).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  have hd : (E.d : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne E.d)
  have hterm : ∀ b c r, post₁ E (joinPhys E.d B a (b, c, r)) *
        star (post₁ E (joinPhys E.d B a' (b, c, r))) =
      ((E.d : ℂ)⁻¹ * E.p' (E.idx r).1) *
        ((schmidtX (D := D) (E.idx c).1 (restrictX (join B a b)) *
            star (schmidtX (D := D) (E.idx c).1 (restrictX (join B a' b)))) *
          (schmidtW (D := D) (E.idx r).1 (join B a b) *
            star (schmidtW (D := D) (E.idx r).1 (join B a' b)))) := fun b c r => by
    simp only [post₁, BXC, ψ, physPart_joinPhys, joinPhys_C, joinPhys_R, star_mul']
    have h1 := ofReal_mul_star_ofReal_sqrt (Nat.cast_nonneg (α := ℝ) E.d)
    have h2 := ofReal_mul_star_ofReal_sqrt (E.p'_nonneg h11 (E.idx r).1)
    have h3 : (((Real.sqrt E.d)⁻¹ : ℝ) : ℂ) * star (((Real.sqrt E.d)⁻¹ : ℝ) : ℂ) =
        (E.d : ℂ)⁻¹ := by
      rw [Complex.ofReal_inv, star_inv₀, ← mul_inv, h1, Complex.ofReal_natCast]
    calc _ = ((((Real.sqrt E.d)⁻¹ : ℝ) : ℂ) * star (((Real.sqrt E.d)⁻¹ : ℝ) : ℂ)) *
          ((Real.sqrt (E.p' (E.idx r).1) : ℂ) * star (Real.sqrt (E.p' (E.idx r).1) : ℂ)) *
          ((schmidtX (D := D) (E.idx c).1 (restrictX (join B a b)) *
            star (schmidtX (D := D) (E.idx c).1 (restrictX (join B a' b)))) *
          (schmidtW (D := D) (E.idx r).1 (join B a b) *
            star (schmidtW (D := D) (E.idx r).1 (join B a' b)))) := by ring
      _ = _ := by rw [h3, h2]
  simp only [hterm]
  set S : Reg (fun v => Fin (n v)) X → ℂ := fun i =>
    ∑ b, schmidtW (D := D) i (join B a b) * star (schmidtW (D := D) i (join B a' b))
  calc _ = ∑ c : Fin E.d, ∑ r : Fin E.d,
        ((E.d : ℂ)⁻¹ * E.p' (E.idx r).1) * ((dimReg n X : ℂ)⁻¹ * S (E.idx r).1) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [← Finset.mul_sum, sum_schmidtX_mul_schmidtW h11 hB _ _ _ _ a a', if_pos rfl]
    _ = ∑ r : Fin E.d, (E.p' (E.idx r).1 : ℂ) * ((dimReg n X : ℂ)⁻¹ * S (E.idx r).1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        field_simp
    _ = _ := by
        rw [← Finset.sum_coe_sort E.E]
        exact E.idx.sum_comp (fun i => (E.p' i.1 : ℂ) * ((dimReg n X : ℂ)⁻¹ * S i.1))

theorem posSemidef_ω (i : Reg (fun v => Fin (n v)) X) (B : Finset σ) :
    (ω D X i B).PosSemidef := by
  rw [ω, show ((dimReg n X : ℂ))⁻¹ = (((dimReg n X : ℝ))⁻¹ : ℝ) by push_cast; rfl,
    Complex.coe_smul]
  exact (TensorPower.posSemidef_vecMarginal _ _ B).smul (by positivity)

theorem trace_ω [∀ v, NeZero (n v)] (h11 : Step_8_11.{u}) {i : Reg (fun v => Fin (n v)) X}
    (hi : 0 < D.p X i) (B : Finset σ) : (ω D X i B).trace = 1 := by
  have hN : (dimReg n X : ℂ) ≠ 0 := by
    rw [dimReg_eq_card]; exact_mod_cast Fintype.card_ne_zero
  have h := (h11 D X).2.2.1 i i hi hi
  rw [if_pos rfl] at h
  rw [ω, trace_smul, TensorPower.trace_vecMarginal, smul_eq_mul,
    Finset.sum_congr rfl fun x _ => mul_comm _ _, h, inv_mul_cancel₀ hN]

theorem posSemidef_ρψ (E : TypicalSet D X) (B : Finset σ) : (ρψ E B).PosSemidef :=
  (TensorPower.posSemidef_vecMarginal _ _ _).submatrix _

theorem posSemidef_sum_smul_ω {s : Finset (Reg (fun v => Fin (n v)) X)}
    {c : Reg (fun v => Fin (n v)) X → ℝ} (hc : ∀ i ∈ s, 0 ≤ c i) (B : Finset σ) :
    (∑ i ∈ s, (c i : ℂ) • ω D X i B).PosSemidef := by
  refine Finset.sum_induction _ PosSemidef (fun _ _ ha hb => ha.add hb) PosSemidef.zero
    fun i hi => ?_
  rw [Complex.coe_smul]
  exact (posSemidef_ω i B).smul (hc i hi)

theorem trace_sum_smul_ω [∀ v, NeZero (n v)] (h11 : Step_8_11.{u})
    (s : Finset (Reg (fun v => Fin (n v)) X)) (B : Finset σ) :
    (∑ i ∈ s, (D.p X i : ℂ) • ω D X i B).trace = ∑ i ∈ s, (D.p X i : ℂ) := by
  rw [trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [trace_smul, smul_eq_mul]
  rcases ((h11 D X).2.2.2.1 i).lt_or_eq with hi | hi
  · rw [trace_ω h11 hi, mul_one]
  · rw [← hi]; simp

theorem TypicalSet.z_le_one (h11 : Step_8_11.{u}) (E : TypicalSet D X) : E.z ≤ 1 := by
  rw [← (h11 D X).2.2.2.2]
  exact Finset.sum_le_univ_sum_of_nonneg fun i => (h11 D X).2.2.2.1 i

theorem TypicalSet.z_mul_p' (E : TypicalSet D X) (i : Reg (fun v => Fin (n v)) X) :
    E.z * E.p' i = D.p X i := by
  rw [TypicalSet.p', mul_div_cancel₀ _ E.z_pos.ne']

theorem trace_ρψ [∀ v, NeZero (n v)] (h11 : Step_8_11.{u}) (E : TypicalSet D X) {B : Finset σ}
    (hB : Disjoint B X) : (ρψ E B).trace = 1 := by
  rw [ρψ_eq_sum_ω h11 hB E, trace_sum]
  have : ∀ i ∈ E.E, ((E.p' i : ℂ) • ω D X i B).trace = (E.p' i : ℂ) := fun i hi => by
    rw [trace_smul, trace_ω h11 (E.p_pos i hi), smul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl this, ← Complex.ofReal_sum]
  simp only [TypicalSet.p', ← Finset.sum_div]
  rw [show ∑ i ∈ E.E, D.p X i = E.z from rfl, div_self E.z_pos.ne', Complex.ofReal_one]

theorem state_restrict_M (B : Finset σ) :
    (D.state.restrict (Finset.subset_univ B)).M = D.ρ B := rfl

/-- D8.17 (`comparator:post-marginal`). For physical `B` disjoint from `X`:
`ρ_B = z ρ_{ψ,B} + (1 - z) ρ_{rem,B}`, `ρ_{ψ,B} ≤ z^{-1} ρ_B`, `S(ρ_{ψ,B}) ≤ S(B)/z`. -/
theorem step_8_17 [∀ v, NeZero (n v)] (h11 : Step_8_11.{u}) (E : TypicalSet D X)
    {B : Finset σ} (hB : Disjoint B X) :
    (∃ ρrem : Matrix (Reg (fun v => Fin (n v)) B) (Reg (fun v => Fin (n v)) B) ℂ,
      ρrem.PosSemidef ∧ ρrem.trace = 1 ∧ D.ρ B = E.z • ρψ E B + (1 - E.z) • ρrem) ∧
    ρψ E B ≤ E.z⁻¹ • D.ρ B ∧
    vonNeumann (posSemidef_ρψ E B).isHermitian ≤ D.S B / E.z ∧
    ∀ (k : ℕ) (h : IrrepLabel (Equiv.Perm (Fin k)) → ℝ),
      star (post E k) ⬝ᵥ
          (labelObservable (Replicas.copyPerm (fun f => Fin (dims n E.d f)) k (physReg B)) h *ᵥ
            post E k) =
        (TensorPower.tensorPow (ρψ E B) *
          labelObservable (TensorPower.copyPerm (Reg (fun v => Fin (n v)) B) k) h).trace ∧
      TensorPower.tensorPow (k := k) (ρψ E B) ≤
        (E.z⁻¹ ^ k) • TensorPower.tensorPow (k := k) (D.ρ B) := by
  have hz := E.z_pos
  have hz1 := E.z_le_one h11
  have hp := (h11 D X).2.2.2.1
  -- D8.17.1: `ρ_B = ∑_i p_i ω_{i,B}`, `ρ_{ψ,B} = ∑_{i ∈ E} p'_i ω_{i,B}`
  have hρ : D.ρ B = ∑ i, (D.p X i : ℂ) • ω D X i B := ρ_eq_sum_ω h11 hB
  have hψ : ρψ E B = ∑ i ∈ E.E, (E.p' i : ℂ) • ω D X i B := ρψ_eq_sum_ω h11 hB E
  -- D8.17.1: `z ρ_{ψ,B} = ∑_{i ∈ E} p_i ω_{i,B}`, so `ρ_B = z ρ_{ψ,B} + ∑_{i ∉ E} p_i ω_{i,B}`
  have hzψ : E.z • ρψ E B = ∑ i ∈ E.E, (D.p X i : ℂ) • ω D X i B := by
    rw [hψ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Complex.coe_smul, smul_smul, ← Complex.ofReal_mul, E.z_mul_p']
  have hsplit : D.ρ B = E.z • ρψ E B + ∑ i ∈ E.Eᶜ, (D.p X i : ℂ) • ω D X i B := by
    rw [hzψ, hρ, Finset.sum_add_sum_compl]
  set R := ∑ i ∈ E.Eᶜ, (D.p X i : ℂ) • ω D X i B
  have hR : R.PosSemidef := posSemidef_sum_smul_ω (fun i _ => hp i) B
  have htrR : R.trace = ((1 - E.z : ℝ) : ℂ) := by
    rw [trace_sum_smul_ω h11, ← Complex.ofReal_sum, ← (h11 D X).2.2.2.2,
      ← Finset.sum_add_sum_compl E.E (D.p X)]
    simp [TypicalSet.z]
  have htrψ : (ρψ E B).trace = 1 := by
    rw [hψ, trace_sum]
    have : ∀ i ∈ E.E, ((E.p' i : ℂ) • ω D X i B).trace = (E.p' i : ℂ) := fun i hi => by
      rw [trace_smul, trace_ω h11 (E.p_pos i hi), smul_eq_mul, mul_one]
    rw [Finset.sum_congr rfl this, ← Complex.ofReal_sum]
    simp only [TypicalSet.p', ← Finset.sum_div]
    rw [show ∑ i ∈ E.E, D.p X i = E.z from rfl, div_self hz.ne', Complex.ofReal_one]
  -- D8.17.1: `ρ_rem = (1 - z)^{-1} ∑_{i ∉ E} p_i ω_{i,B}` (remainder omitted if `z = 1`)
  obtain ⟨ρrem, hrem, htrrem, hdecomp⟩ : ∃ ρrem : Matrix (Reg (fun v => Fin (n v)) B)
      (Reg (fun v => Fin (n v)) B) ℂ, ρrem.PosSemidef ∧ ρrem.trace = 1 ∧
      D.ρ B = E.z • ρψ E B + (1 - E.z) • ρrem := by
    rcases hz1.lt_or_eq with hz1 | hz1
    · have h1z : (0 : ℝ) < 1 - E.z := sub_pos.mpr hz1
      refine ⟨(1 - E.z)⁻¹ • R, hR.smul (inv_nonneg.mpr h1z.le), ?_, ?_⟩
      · rw [trace_smul, htrR, Complex.real_smul, ← Complex.ofReal_mul,
          inv_mul_cancel₀ h1z.ne', Complex.ofReal_one]
      · rw [smul_smul, mul_inv_cancel₀ h1z.ne', one_smul, hsplit]
    · refine ⟨ρψ E B, posSemidef_ρψ E B, htrψ, ?_⟩
      have hR0 : R = 0 := by
        have h0 : ∀ i ∈ E.Eᶜ, D.p X i = 0 := by
          refine (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hp i).mp ?_
          have := congrArg Complex.re htrR
          rw [trace_sum_smul_ω h11, ← Complex.ofReal_sum, Complex.ofReal_re,
            Complex.ofReal_re, hz1, sub_self] at this
          exact this
        exact Finset.sum_eq_zero fun i hi => by rw [h0 i hi]; simp
      rw [hsplit, hR0, ← hz1, sub_self, zero_smul, add_zero]
  -- D8.17.2: `(1 - z) ρ_rem ≥ 0`, hence `ρ_{ψ,B} ≤ z^{-1} ρ_B`
  have hdom : ρψ E B ≤ E.z⁻¹ • D.ρ B := by
    rw [hsplit, smul_add, smul_smul, inv_mul_cancel₀ hz.ne', one_smul, le_add_iff_nonneg_right]
    exact (hR.smul (inv_nonneg.mpr hz.le)).nonneg
  -- D8.17.3: concavity, `S(B) ≥ z S(ρ_{ψ,B}) + (1 - z) S(ρ_rem) ≥ z S(ρ_{ψ,B})`
  have hent : vonNeumann (posSemidef_ρψ E B).isHermitian ≤ D.S B / E.z := by
    let τ : Fin 2 → Arealaw.MState (Reg (fun v => Fin (n v)) B) ℂ :=
      ![Arealaw.MState.mk' (posSemidef_ρψ E B) (by rw [htrψ]; simp),
        Arealaw.MState.mk' hrem (by rw [htrrem]; simp)]
    have hc := Arealaw.MState.sum_mul_entropy_le_entropy (p := ![E.z, 1 - E.z])
      (fun i => by fin_cases i <;> simp [hz.le, hz1]) (by simp) τ
      (D.state.restrict (Finset.subset_univ B)) (by
        rw [state_restrict_M, hdecomp, Fin.sum_univ_two]
        simp only [τ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
          Arealaw.MState.mk'_M, Complex.coe_smul])
    have h0 : 0 ≤ (τ 1).entropy := Arealaw.SubState.entropy_nonneg _
    have h0' : (τ 0).entropy = vonNeumann (posSemidef_ρψ E B).isHermitian := rfl
    rw [Fin.sum_univ_two, h0'] at hc
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hc
    rw [le_div_iff₀ hz, mul_comm]
    have : D.S B = (D.state.restrict (Finset.subset_univ B)).entropy := rfl
    rw [this]
    nlinarith [mul_nonneg (sub_nonneg.mpr hz1) h0]
  refine ⟨⟨ρrem, hrem, htrrem, hdecomp⟩, hdom, hent, fun k h => ⟨?_, ?_⟩⟩
  -- Output: the `B`-marginal of `post_k` is `ρ_{ψ,B}^{⊗k}`
  · rw [post_eq_tensorVec]
    have e1 := TensorPower.dotProduct_labelObservable_mulVec_prod (fun f => Fin (dims n E.d f))
      (post₁ E) (physReg B) k h
    refine e1.trans ?_
    set e := Equiv.arrowCongr (Equiv.refl (Fin k)) (regPhys (n := n) E.d B)
    have hL : labelObservable (TensorPower.copyPerm
          (TensorPower.SubConfig (fun f => Fin (dims n E.d f)) (physReg B)) k) h =
        (labelObservable (TensorPower.copyPerm (Reg (fun v => Fin (n v)) B) k) h).submatrix
          e.symm e.symm := by
      ext x y
      simp only [labelObservable, Matrix.sum_apply, Matrix.smul_apply, submatrix_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [labelProj_of_intertwine (φ := TensorPower.copyPerm (Reg (fun v => Fin (n v)) B) k) e
        (fun g x => rfl) l]
      rfl
    have hT : TensorPower.tensorPow (k := k)
          (TensorPower.vecMarginal (fun f => Fin (dims n E.d f)) (post₁ E) (physReg B)) =
        (TensorPower.tensorPow (k := k) (ρψ E B)).submatrix e.symm e.symm := by
      ext x y
      simp [ρψ, TensorPower.tensorPow_apply, e, Equiv.arrowCongr_apply]
    rw [hL, hT, submatrix_mul_equiv, trace_submatrix]
  -- Output: `ρ_{ψ,B}^{⊗k} ≤ z^{-k} ρ_B^{⊗k}`
  · rw [← TensorPower.tensorPow_real_smul]
    exact TensorPower.tensorPow_le_tensorPow (posSemidef_ρψ E B) hdom

end PostMarginal

/-! ## D8.18–D8.20 The rough upper bound -/

section Rough

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} {D : PhysData n} {X : Finset σ}

/-- `{F_B ≤ c}`: the spectral projection of the label observable of the physical region `B`. -/
noncomputable def cutProj (d k : ℕ) (B : Finset σ) (c : ℝ) :
    Matrix (Transport.Config (dims n d) k) (Transport.Config (dims n d) k) ℂ :=
  labelObservable (Replicas.copyPerm (fun f => Fin (dims n d f)) k (physReg B))
    fun l => if Real.log l.dim ≤ c then 1 else 0

omit [Fintype σ] [DecidableEq σ] in
theorem physReg_subset {B B' : Finset σ} (h : B ⊆ B') : physReg B ⊆ physReg B' :=
  Finset.map_subset_map.mpr h

omit [Fintype σ] [DecidableEq σ] in
theorem disjoint_physReg {B B' : Finset σ} (h : Disjoint B B') :
    Disjoint (physReg B) (physReg B') :=
  (Finset.disjoint_map _).mpr h

omit [Fintype σ] [DecidableEq σ] in
theorem disjoint_physReg_R (B : Finset σ) : Disjoint (physReg B) {Site.R} :=
  Finset.disjoint_singleton_right.mpr (Upper.R_not_mem_physReg B)

omit [Fintype σ] in
theorem Upper.disjoint_physReg_XC {B : Finset σ} (h : Disjoint B X) :
    Disjoint (physReg B) (XC X) := by
  rw [XC, Finset.disjoint_insert_right]
  exact ⟨Upper.C_not_mem_physReg B, disjoint_physReg h⟩

omit [Fintype σ] in
theorem Upper.R_not_mem_XC : Site.R ∉ XC X := by simp [XC, Upper.R_not_mem_physReg]

variable (n) in
/-- Label functions of any region preserve `𝒮_k`. -/
theorem Upper.labelObservable_mulVec_mem_S (d k : ℕ) (Q : Finset (Site σ))
    (g : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) {v : Transport.Config (dims n d) k → ℂ}
    (hv : v ∈ Replicas.S (fun f => Fin (dims n d f)) k) :
    labelObservable (Replicas.copyPerm (fun f => Fin (dims n d f)) k Q) g *ᵥ v ∈
      Replicas.S (fun f => Fin (dims n d f)) k := by
  rw [Replicas.S_eq] at hv ⊢
  intro τ
  rw [mulVec_mulVec, (TensorPower.commute_copyPerm_labelObservable (n := dims n d) k Q g τ).eq,
    ← mulVec_mulVec, hv τ]

/-- `B_{XC}` reads only the factors `XC`. -/
theorem Upper.BXC_congr (E : TypicalSet D X) {x x' : SiteConfig (dims n E.d)}
    (h : ∀ f ∈ XC X, x f = x' f) : BXC E x = BXC E x' := by
  have hC : x .C = x' .C := h _ (Finset.mem_insert_self _ _)
  have hX : restrictX (X := X) (physPart x) = restrictX (physPart x') := by
    funext v
    exact h _ (Finset.mem_insert_of_mem (Upper.phys_mem_physReg.mpr v.2))
  simp only [BXC, hC, hX]

/-- `𝖯` commutes with label functions of regions disjoint from `XC`. -/
theorem Upper.commute_pinProj_labelObservable (E : TypicalSet D X) (k : ℕ) {Q : Finset (Site σ)}
    (hQ : Disjoint Q (XC X)) (g : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) :
    Commute (pinProj E k)
      (labelObservable (Replicas.copyPerm (fun f => Fin (dims n E.d f)) k Q) g) := by
  refine (commute_labelObservable_of_forall_commute _ (fun τ => ?_) g).symm
  refine commute_permOp_of_apply _ τ fun x y => ?_
  have hfix : ∀ (z : Transport.Config (dims n E.d) k) j, ∀ f ∈ XC X,
      (Replicas.copyPerm (fun f => Fin (dims n E.d f)) k Q τ z) j f = z j f := by
    intro z j f hf
    rw [Replicas.copyPerm_apply, if_neg (Finset.disjoint_right.mp hQ hf)]
  have hB : ∀ (z : Transport.Config (dims n E.d) k) j,
      BXC E ((Replicas.copyPerm (fun f => Fin (dims n E.d f)) k Q τ z) j) = BXC E (z j) :=
    fun z j => Upper.BXC_congr E (hfix z j)
  have hagree : (∀ j, ∀ f ∉ XC X, (Replicas.copyPerm (fun f => Fin (dims n E.d f)) k Q τ x) j f =
      (Replicas.copyPerm (fun f => Fin (dims n E.d f)) k Q τ y) j f) ↔
      ∀ j, ∀ f ∉ XC X, x j f = y j f := by
    simp only [Replicas.copyPerm_apply]
    constructor
    · intro h j f hf
      by_cases hfQ : f ∈ Q
      · have := h (τ j) f hf
        simpa [hfQ] using this
      · simpa [hfQ] using h j f hf
    · intro h j f hf
      by_cases hfQ : f ∈ Q <;> simp [hfQ, h _ f hf]
  simp only [pinProj, hB, hagree]

/-- One copy of `𝖯`: the projection of `XC` onto `B_{XC}`. -/
noncomputable def pinProj₁ (E : TypicalSet D X) :
    Matrix (SiteConfig (dims n E.d)) (SiteConfig (dims n E.d)) ℂ :=
  Matrix.of fun x y => BXC E x * star (BXC E y) * if ∀ f ∉ XC X, x f = y f then 1 else 0

theorem Upper.pinProj_eq_tensorPow (E : TypicalSet D X) (k : ℕ) :
    pinProj E k = TensorPower.tensorPow (k := k) (pinProj₁ E) := by
  ext x y
  rw [TensorPower.tensorPow_apply]
  simp only [pinProj, pinProj₁, of_apply, Finset.prod_mul_distrib, Finset.prod_boole,
    Finset.mem_univ, true_implies]

theorem card_complConfig_compl (X : Finset σ) :
    Fintype.card (TensorPower.ComplConfig (fun v => Fin (n v)) (Finset.univ \ X)) =
      Fintype.card (Reg (fun v => Fin (n v)) X) :=
  Fintype.card_congr
    { toFun := fun b v => b ⟨v.1, by simp [v.2]⟩
      invFun := fun y v => y ⟨v.1, by simpa using v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- `ψ` reads only the factors outside `XC` (`w_i` is constant along `X`). -/
theorem ψ_congr (h11 : Step_8_11.{u}) (E : TypicalSet D X) {x w : SiteConfig (dims n E.d)}
    (h : ∀ f ∉ XC X, x f = w f) : ψ E w = ψ E x := by
  have hR : w .R = x .R := (h _ Upper.R_not_mem_XC).symm
  have hw : physPart w = replaceX (physPart x) (restrictX (X := X) (physPart w)) := by
    funext v
    unfold replaceX
    split
    · rfl
    · rename_i hv
      exact (h _ fun hf => by
        rcases Finset.mem_insert.mp hf with hf | hf
        · cases hf
        · exact hv (Upper.phys_mem_physReg.mp hf)).symm
  simp only [ψ, hR]
  rw [hw, (h11 D X).2.1]

/-- The `R`-entry of a configuration of `𝒱`. -/
def rOf (d : ℕ) (x : SiteConfig (dims n d)) : Fin d := x .R

/-- The physical part of a configuration of `𝒱` on `B`. -/
def physRestr (d : ℕ) (B : Finset σ) (x : SiteConfig (dims n d)) : Reg (fun v => Fin (n v)) B :=
  fun v => x (.phys v.1)

theorem agree_joinPhys_iff (d : ℕ) (x : SiteConfig (dims n d))
    (a : Reg (fun v => Fin (n v)) (Finset.univ \ X))
    (q : TensorPower.ComplConfig (fun v => Fin (n v)) (Finset.univ \ X) × Fin d × Fin d) :
    (∀ f ∉ XC X, x f = joinPhys d (Finset.univ \ X) a q f) ↔
      (a = physRestr d (Finset.univ \ X) x ∧ q.2.2 = rOf d x) := by
  constructor
  · intro h
    refine ⟨funext fun v => ?_, ?_⟩
    · change a v = x (.phys v.1)
      have hv : v.1 ∉ X := (Finset.mem_sdiff.mp v.2).2
      have := h (.phys v.1) fun hf => by
        rcases Finset.mem_insert.mp hf with hf | hf
        · cases hf
        · exact hv (Upper.phys_mem_physReg.mp hf)
      rw [joinPhys_phys _ _ _ _ v.2] at this
      exact this.symm
    · have := h .R Upper.R_not_mem_XC
      rw [joinPhys_R] at this
      exact this.symm
  · rintro ⟨rfl, hr⟩ f hf
    rcases f with v | _ | _
    · have hv : v ∈ Finset.univ \ X := Finset.mem_sdiff.mpr ⟨Finset.mem_univ v,
        fun hv => hf (Finset.mem_insert_of_mem (Upper.phys_mem_physReg.mpr hv))⟩
      rw [joinPhys_phys _ _ _ _ hv]
      rfl
    · exact absurd (Finset.mem_insert_self _ _) hf
    · rw [joinPhys_R, hr]
      rfl

/-- `∑_y |⟨y|i⟩|² = 1`, summed over the `X`-parts of the configurations of `X^c`. -/
theorem sum_star_schmidtX_complRestr [∀ v, NeZero (n v)] (i : Reg (fun v => Fin (n v)) X) :
    ∑ b, star (schmidtX (D := D) i (TensorPower.complRestr (fun v => Fin (n v))
        (Finset.disjoint_sdiff : Disjoint X (Finset.univ \ X)) b)) *
      schmidtX (D := D) i (TensorPower.complRestr (fun v => Fin (n v))
        (Finset.disjoint_sdiff : Disjoint X (Finset.univ \ X)) b) = 1 := by
  have hN : (Fintype.card (TensorPower.SubConfig (fun v => Fin (n v)) X) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have key := TensorPower.card_mul_sum_complRestr_mul (fun v => Fin (n v))
    (Finset.disjoint_sdiff : Disjoint X (Finset.univ \ X))
    (fun y => star (schmidtX (D := D) i y) * schmidtX (D := D) i y) (fun _ => 1)
    (fun _ _ => rfl)
  have h1 : ∑ y, star (schmidtX (D := D) i y) * schmidtX (D := D) i y = 1 := by
    have := sum_schmidtX_mul_star (D := D) i i
    rw [if_pos rfl] at this
    rw [← this]
    exact Finset.sum_congr rfl fun y _ => mul_comm _ _
  simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, h1, one_mul] at key
  rw [card_complConfig_compl X] at key
  exact mul_left_cancel₀ hN (key.trans (mul_one _).symm)

/-- `∑_{w ~ x} |B_{XC}(w)|² = 1`, the sum over the configurations of `XC`. -/
theorem sum_agree_BXC [∀ v, NeZero (n v)] (E : TypicalSet D X) (x : SiteConfig (dims n E.d)) :
    ∑ w, (if ∀ f ∉ XC X, x f = w f then (1 : ℂ) else 0) * (star (BXC E w) * BXC E w) = 1 := by
  have hXB : Disjoint X (Finset.univ \ X) := Finset.disjoint_sdiff
  have hd : (E.d : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne E.d)
  rw [← (splitPhys E.d (Finset.univ \ X)).sum_comp]
  set a₀ := physRestr E.d (Finset.univ \ X) x
  classical
  have key : ∀ p, (if ∀ f ∉ XC X, x f = splitPhys E.d (Finset.univ \ X) p f then (1 : ℂ) else 0) *
      (star (BXC E (splitPhys E.d (Finset.univ \ X) p)) *
        BXC E (splitPhys E.d (Finset.univ \ X) p)) =
      if p.1 = a₀ ∧ p.2.2.2 = rOf E.d x then
        star (BXC E (joinPhys E.d (Finset.univ \ X) p.1 p.2)) *
          BXC E (joinPhys E.d (Finset.univ \ X) p.1 p.2) else 0 := by
    intro p
    by_cases hp : ∀ f ∉ XC X, x f = splitPhys E.d (Finset.univ \ X) p f
    · rw [if_pos hp, if_pos ((agree_joinPhys_iff E.d x p.1 p.2).mp hp), one_mul]; rfl
    · rw [if_neg hp, if_neg (fun h => hp ((agree_joinPhys_iff E.d x p.1 p.2).mpr h)), zero_mul]
  rw [Finset.sum_congr rfl fun p _ => key p, Fintype.sum_prod_type,
    Finset.sum_eq_single a₀ (fun a _ ha => Finset.sum_eq_zero fun q _ => by
      rw [if_neg (fun h => ha h.1)]) (by simp)]
  have hterm : ∀ q : TensorPower.ComplConfig (fun v => Fin (n v)) (Finset.univ \ X) ×
      Fin E.d × Fin E.d,
      (if a₀ = a₀ ∧ q.2.2 = rOf E.d x then
        star (BXC E (joinPhys E.d (Finset.univ \ X) a₀ q)) *
          BXC E (joinPhys E.d (Finset.univ \ X) a₀ q) else 0) =
      if q.2.2 = rOf E.d x then (E.d : ℂ)⁻¹ *
        (star (schmidtX (D := D) (E.idx q.2.1).1 (TensorPower.complRestr _ hXB q.1)) *
          schmidtX (D := D) (E.idx q.2.1).1 (TensorPower.complRestr _ hXB q.1)) else 0 := by
    intro q
    by_cases hq : q.2.2 = rOf E.d x
    · rw [if_pos ⟨rfl, hq⟩, if_pos hq]
      simp only [BXC, joinPhys_C, physPart_joinPhys, restrictX_join hXB, star_mul']
      have h1 := ofReal_mul_star_ofReal_sqrt (Nat.cast_nonneg (α := ℝ) E.d)
      have h3 : star (((Real.sqrt E.d)⁻¹ : ℝ) : ℂ) * (((Real.sqrt E.d)⁻¹ : ℝ) : ℂ) =
          (E.d : ℂ)⁻¹ := by
        rw [mul_comm, Complex.ofReal_inv, star_inv₀, ← mul_inv, h1, Complex.ofReal_natCast]
      rw [← h3]
      ring
    · rw [if_neg (fun h => hq h.2), if_neg hq]
  rw [Finset.sum_congr rfl fun q _ => hterm q, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, sum_star_schmidtX_complRestr, mul_one]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_inv_cancel₀ hd]

theorem pinProj₁_mulVec_post₁ [∀ v, NeZero (n v)] (h11 : Step_8_11.{u}) (E : TypicalSet D X) :
    pinProj₁ E *ᵥ post₁ E = post₁ E := by
  funext x
  have e : ∀ w, pinProj₁ E x w * post₁ E w =
      (BXC E x * ψ E x) * ((if ∀ f ∉ XC X, x f = w f then (1 : ℂ) else 0) *
        (star (BXC E w) * BXC E w)) := fun w => by
    simp only [pinProj₁, of_apply, post₁]
    split_ifs with hw
    · rw [ψ_congr h11 E hw]; ring
    · ring
  change ∑ w, pinProj₁ E x w * post₁ E w = post₁ E x
  simp only [e]
  rw [← Finset.mul_sum, sum_agree_BXC E x, mul_one]
  rfl

/-- `𝖯 post_k = post_k`. -/
theorem pinProj_mulVec_post [∀ v, NeZero (n v)] (h11 : Step_8_11.{u}) (E : TypicalSet D X)
    (k : ℕ) : pinProj E k *ᵥ post E k = post E k := by
  rw [Upper.pinProj_eq_tensorPow, post_eq_tensorVec, TensorPower.tensorPow_mulVec_tensorVec,
    pinProj₁_mulVec_post₁ h11 E]

/-- `post_k ∈ 𝒮_k`. -/
theorem post_mem_S (E : TypicalSet D X) (k : ℕ) :
    post E k ∈ Replicas.S (fun f => Fin (dims n E.d f)) k := by
  rw [Replicas.S_eq, post_eq_tensorVec]
  exact TensorPower.tensorVec_mem_symmetricSubspace _

/-! ### D8.18 Rough overlap -/

/-- D8.18.2 at the label level: under an iid density `ρ^{⊗k}` the label cutoff
`{F > k c}`, `c ≥ S(ρ) + 1`, has probability `≤ poly(k) e^{-u₀ k}` (exponential Markov with the
moment bound of D8.10 at a fixed small `u`). -/
theorem tail_bound (h10 : Step_8_10.{u}) {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
    {ρ : Matrix Ω Ω ℂ} (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    ∃ u₀ C N : ℝ, 0 < u₀ ∧ ∀ (k : ℕ) (c : ℝ), vonNeumann hρ.isHermitian + 1 ≤ c →
      (TensorPower.tensorPow (k := k) ρ * labelObservable (TensorPower.copyPerm Ω k)
          (fun l => if Real.log l.dim ≤ k * c then 0 else 1)).trace.re ≤
        C * ((k : ℝ) + 1) ^ N * Real.exp (-(u₀ * k)) := by
  obtain ⟨𝓑, h𝓑, hmgf⟩ := exists_mgf_bound hρ htr
  obtain ⟨c₁, hc₁, H⟩ := h10 1 1 one_pos one_pos
  obtain ⟨Cp, Np, hk⟩ := H ρ hρ htr 𝓑 (vonNeumann hρ.isHermitian) h𝓑 hmgf
  have hs : 0 < Real.sqrt 𝓑 := Real.sqrt_pos.mpr (by linarith)
  set u₁ := min (c₁ / Real.sqrt 𝓑) (1 / (4 * 𝓑))
  have hu₁ : 0 < u₁ := lt_min (div_pos hc₁ hs) (by positivity)
  refine ⟨u₁ / 2, Real.exp Cp, Np, by positivity, fun k c hc => ?_⟩
  set S := vonNeumann hρ.isHermitian
  have hρk := TensorPower.posSemidef_tensorPow_of_posSemidef (k := k) hρ
  have hm := hk k u₁ hu₁.le (min_le_left _ _) 1 (Or.inl rfl)
  rw [cfc_labelObservable] at hm
  set g : IrrepLabel (Equiv.Perm (Fin k)) → ℝ :=
    (fun x => Real.exp (1 * u₁ * (x - k * S))) ∘ fun l => Real.log l.dim
  have hT := (Real.le_exp_log _).trans (Real.exp_le_exp.mpr hm)
  have hpt : ∀ l : IrrepLabel (Equiv.Perm (Fin k)),
      (if Real.log l.dim ≤ k * c then 0 else 1) ≤ Real.exp (-(u₁ * k)) * g l := by
    intro l
    split_ifs with hl
    · simp only [g, Function.comp]
      positivity
    · simp only [g, Function.comp, one_mul, ← Real.exp_add]
      apply Real.one_le_exp
      push Not at hl
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have h1 : (k : ℝ) * (S + 1) ≤ k * c := mul_le_mul_of_nonneg_left hc hk0
      have h2 : (k : ℝ) ≤ Real.log l.dim - k * S := by linarith
      have h3 := mul_le_mul_of_nonneg_left h2 hu₁.le
      linarith
  have hmono := hρk.re_trace_mul_mono
    (labelObservable_le_labelObservable (TensorPower.copyPerm Ω k) hpt)
  rw [labelObservable_const_mul, mul_smul_comm, trace_smul, Complex.smul_re, smul_eq_mul] at hmono
  have hu4 : 𝓑 * u₁ ≤ 1 / 4 := by
    have := min_le_right (c₁ / Real.sqrt 𝓑) (1 / (4 * 𝓑))
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  calc _ ≤ Real.exp (-(u₁ * k)) * (TensorPower.tensorPow (k := k) ρ *
        labelObservable (TensorPower.copyPerm Ω k) g).trace.re := hmono
    _ ≤ Real.exp (-(u₁ * k)) * Real.exp (2 * 1 * k * 𝓑 * u₁ ^ 2 + Cp + Np * Real.log (k + 1)) :=
        mul_le_mul_of_nonneg_left hT (Real.exp_pos _).le
    _ ≤ Real.exp Cp * ((k : ℝ) + 1) ^ Np * Real.exp (-(u₁ / 2 * k)) := by
        rw [Real.rpow_def_of_pos (by positivity), ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have h5 : 2 * 1 * k * 𝓑 * u₁ ^ 2 = (2 * k * u₁) * (𝓑 * u₁) := by ring
        have h6 : (2 * k * u₁) * (𝓑 * u₁) ≤ (2 * k * u₁) * (1 / 4) :=
          mul_le_mul_of_nonneg_left hu4 (by positivity)
        have : 2 * 1 * k * 𝓑 * u₁ ^ 2 ≤ u₁ / 2 * k := by linarith
        linarith

/-- D8.18.2 for `post_k`: `‖{F_B > k(S(B)/z + 1)} post_k‖² ≤ poly(k) e^{-u₀ k}`. -/
theorem post_tail [∀ v, NeZero (n v)] (h10 : Step_8_10.{u}) (h11 : Step_8_11.{u})
    (E : TypicalSet D X) {B : Finset σ} (hB : Disjoint B X) :
    ∃ u₀ C N : ℝ, 0 < u₀ ∧ ∀ k : ℕ,
      (star (post E k) ⬝ᵥ ((1 - cutProj E.d k B (k * (D.S B / E.z + 1))) *ᵥ post E k)).re ≤
        C * ((k : ℝ) + 1) ^ N * Real.exp (-(u₀ * k)) := by
  obtain ⟨-, -, hent, hout⟩ := step_8_17 h11 E hB
  obtain ⟨u₀, C, N, hu₀, ht⟩ := tail_bound h10 (posSemidef_ρψ E B) (trace_ρψ h11 E hB)
  refine ⟨u₀, C, N, hu₀, fun k => ?_⟩
  rw [cutProj, one_sub_labelObservable_indicator, (hout k _).1]
  refine ht k _ ?_
  have hz := E.z_pos
  linarith

/-- Label functions of physical regions commute with each other when nested or disjoint. -/
theorem commute_cutProj (d k : ℕ) {B B' : Finset σ} (h : B ⊆ B' ∨ B' ⊆ B) (c c' : ℝ) :
    Commute (cutProj (n := n) d k B c) (cutProj d k B' c') := by
  rcases h with h | h
  · exact Replicas.commute_labelObservable _ k (Or.inl (physReg_subset h)) _ _
  · exact (Replicas.commute_labelObservable _ k (Or.inl (physReg_subset h)) _ _).symm

theorem commute_piR_labelObservable (d k : ℕ) (l : IrrepLabel (Equiv.Perm (Fin k)))
    {Q : Finset (Site σ)} (hQ : Disjoint Q {Site.R}) (g : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) :
    Commute (piR (n := n) d k l)
      (labelObservable (Replicas.copyPerm (fun f => Fin (dims n d f)) k Q) g) := by
  rw [piR, Replicas.π, labelProj_eq_labelObservable_ite]
  exact Replicas.commute_labelObservable _ k (Or.inr hQ.symm) _ _

/-- D8.18 (`comparator:rough-overlap`). There is a unit vector `φ` in the common range of the
projections `{F_B ≤ k(S(B)/z + 1)}_{B ∈ 𝓡}` with
`|⟨φ, π_R^{λ_k} post_k⟩|² ≥ poly(k)^{-1}`. -/
theorem step_8_18 [∀ v, NeZero (n v)] (h10 : Step_8_10.{u}) (h11 : Step_8_11.{u})
    (E : TypicalSet D X) {l : ∀ k : ℕ, IrrepLabel (Equiv.Perm (Fin k))} (hl : HighLabel E l)
    (𝓡 : Finset (Finset σ)) (hnest : ∀ B ∈ 𝓡, ∀ B' ∈ 𝓡, B ⊆ B' ∨ B' ⊆ B)
    (hdisj : ∀ B ∈ 𝓡, Disjoint B X) :
    ∃ c N : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∃ φ : Transport.Config (dims n E.d) k → ℂ,
      star φ ⬝ᵥ φ = 1 ∧ φ ∈ Replicas.S (fun f => Fin (dims n E.d f)) k ∧
      pinProj E k *ᵥ φ = φ ∧ (∀ B ∈ 𝓡, cutProj E.d k B (k * (D.S B / E.z + 1)) *ᵥ φ = φ) ∧
      c * ((k : ℝ) + 1) ^ (-N) ≤ ‖star φ ⬝ᵥ (piR E.d k (l k) *ᵥ post E k)‖ ^ 2 := by
  obtain ⟨c, N, hc, ε, -, hq⟩ := hl
  have htail : ∀ B ∈ 𝓡, ∃ u₀ C M : ℝ, 0 < u₀ ∧ ∀ k : ℕ,
      (star (post E k) ⬝ᵥ ((1 - cutProj E.d k B (k * (D.S B / E.z + 1))) *ᵥ post E k)).re ≤
        C * ((k : ℝ) + 1) ^ M * Real.exp (-(u₀ * k)) :=
    fun B hB => post_tail h10 h11 E (hdisj B hB)
  choose! u₀ Cb Mb hu₀ htail using htail
  -- D8.18.3: the finite union over `𝓡` is still exponentially small
  have hev : ∀ᶠ k : ℕ in atTop, ∑ B ∈ 𝓡, Cb B * ((k : ℝ) + 1) ^ Mb B * Real.exp (-(u₀ B * k)) ≤
      c / 2 * ((k : ℝ) + 1) ^ (-N) := by
    have ht : Tendsto (fun k : ℕ => ∑ B ∈ 𝓡,
        Cb B * (((k : ℝ) + 1) ^ (N + Mb B) * Real.exp (-(u₀ B * k)))) atTop (𝓝 0) := by
      have := tendsto_finsetSum 𝓡 fun B hB =>
        (Real.tendsto_natCast_add_one_rpow_mul_exp_neg (N + Mb B) (u₀ B) (hu₀ B hB)).const_mul
          (Cb B)
      simpa using this
    filter_upwards [ht.eventually (gt_mem_nhds (half_pos hc))] with k hk
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [Real.rpow_neg hk1.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hk1 _),
      Finset.sum_mul]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun B _ => ?_)) hk.le
    rw [Real.rpow_add hk1]
    ring
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp hev
  refine ⟨c / 2, N, half_pos hc, k₀, fun k hk => ?_⟩
  set ι := fun f : Site σ => Fin (dims n E.d f)
  set x := piR E.d k (l k) *ᵥ post E k
  set P : Finset σ → Matrix (Transport.Config (dims n E.d) k) (Transport.Config (dims n E.d) k) ℂ :=
    fun B => cutProj E.d k B (k * (D.S B / E.z + 1))
  set Ps := 𝓡.toList.map P
  have hPs : ∀ Q ∈ Ps, Q.IsHermitian ∧ Q * Q = Q := fun Q hQ => by
    obtain ⟨B, -, rfl⟩ := List.mem_map.mp hQ
    exact labelObservable_indicator_proj _ _
  have hcPs : ∀ Q ∈ Ps, ∀ R ∈ Ps, Commute Q R := fun Q hQ R hR => by
    obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hQ
    obtain ⟨B', hB', rfl⟩ := List.mem_map.mp hR
    exact commute_cutProj _ _ (hnest B (Finset.mem_toList.mp hB) B' (Finset.mem_toList.mp hB'))
      _ _
  obtain ⟨hPih, hPiPi⟩ := list_prod_isHermitian_idem Ps hPs hcPs
  set y := Ps.prod *ᵥ x
  -- D8.18.1: the cutoffs commute with `π_R^{λ_k}` and with `𝖯`
  have hπP : ∀ B ∈ 𝓡, Commute (piR E.d k (l k)) (P B) := fun B _ =>
    commute_piR_labelObservable _ _ _ (disjoint_physReg_R B) _
  have hπR := labelObservable_indicator_proj (Replicas.copyPerm ι k {Site.R})
    (fun l' => l' = l k)
  rw [← labelProj_eq_labelObservable_ite] at hπR
  -- D8.18.2: `‖(1 - P_B) x‖² ≤ ⟨post, (1 - P_B) post⟩ ≤ poly(k) e^{-u₀ k}`
  have hterm : ∀ B ∈ 𝓡, (star ((1 - P B) *ᵥ x) ⬝ᵥ ((1 - P B) *ᵥ x)).re ≤
      Cb B * ((k : ℝ) + 1) ^ Mb B * Real.exp (-(u₀ B * k)) := fun B hB => by
    obtain ⟨hPh, hPP⟩ := labelObservable_indicator_proj
      (Replicas.copyPerm ι k (physReg B)) (fun l' => Real.log l'.dim ≤ k * (D.S B / E.z + 1))
    have hQh : (1 - P B).IsHermitian := isHermitian_one.sub hPh
    have hQQ : (1 - P B) * (1 - P B) = 1 - P B := by
      simp only [P, cutProj] at hPP ⊢
      rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, hPP, sub_self, sub_zero]
    have e1 : (1 - P B) *ᵥ x = piR E.d k (l k) *ᵥ ((1 - P B) *ᵥ post E k) := by
      rw [mulVec_mulVec, mulVec_mulVec, ((Commute.one_right _).sub_right (hπP B hB)).eq]
    rw [e1]
    refine (hπR.1.re_dotProduct_mulVec_self_le_of_idem hπR.2 _).trans ?_
    have e2 : (star ((1 - P B) *ᵥ post E k) ⬝ᵥ ((1 - P B) *ᵥ post E k)) =
        star (post E k) ⬝ᵥ ((1 - P B) *ᵥ post E k) := by
      rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hQh.eq, hQQ]
    rw [e2]
    exact htail B hB k
  have hsum := re_dotProduct_self_le_list_prod Ps hPs hcPs x
  rw [List.map_map, Finset.sum_map_toList] at hsum
  have hqk : c * ((k : ℝ) + 1) ^ (-N) ≤ (star x ⬝ᵥ x).re := (hq k).1
  have hy : c / 2 * ((k : ℝ) + 1) ^ (-N) ≤ (star y ⬝ᵥ y).re := by
    have := Finset.sum_le_sum hterm
    simp only [Function.comp] at hsum
    linarith [hk₀ k hk]
  have hy0 : 0 < (star y ⬝ᵥ y).re := lt_of_lt_of_le (by positivity) hy
  set r := Real.sqrt (star y ⬝ᵥ y).re
  have hr : 0 < r := Real.sqrt_pos.mpr hy0
  have hrr : r * r = (star y ⬝ᵥ y).re := Real.mul_self_sqrt hy0.le
  refine ⟨((r⁻¹ : ℝ) : ℂ) • y, ?_, ?_, ?_, ?_, ?_⟩
  -- D8.18.4: `φ = Π_cut x / ‖Π_cut x‖`
  · rw [star_smul, smul_dotProduct, dotProduct_smul, Matrix.star_dotProduct_self_eq_re y,
      Complex.star_def, Complex.conj_ofReal, smul_eq_mul, smul_eq_mul, ← hrr]
    push_cast
    field_simp
  · refine Submodule.smul_mem _ _ (Matrix.list_prod_mulVec_mem _ Ps (fun Q hQ v hv => ?_) ?_)
    · obtain ⟨B, -, rfl⟩ := List.mem_map.mp hQ
      exact Upper.labelObservable_mulVec_mem_S n _ _ _ _ hv
    · change labelProj (Replicas.copyPerm ι k {Site.R}) (l k) *ᵥ post E k ∈ _
      rw [labelProj_eq_labelObservable_ite]
      exact Upper.labelObservable_mulVec_mem_S n _ _ _ _ (post_mem_S E k)
  · have hcomm : Commute (pinProj E k) (Ps.prod * piR E.d k (l k)) := by
      refine Commute.mul_right (Commute.list_prod_right _ _ fun Q hQ => ?_) ?_
      · obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hQ
        exact Upper.commute_pinProj_labelObservable E k
          (Upper.disjoint_physReg_XC (hdisj B (Finset.mem_toList.mp hB))) _
      · rw [piR, Replicas.π, labelProj_eq_labelObservable_ite]
        exact Upper.commute_pinProj_labelObservable E k
          (Finset.disjoint_singleton_left.mpr Upper.R_not_mem_XC) _
    rw [mulVec_smul]
    congr 1
    change pinProj E k *ᵥ (Ps.prod *ᵥ (piR E.d k (l k) *ᵥ post E k)) = _
    rw [mulVec_mulVec, mulVec_mulVec, mul_assoc, hcomm.eq, ← mulVec_mulVec,
      pinProj_mulVec_post h11 E k, ← mulVec_mulVec]
  · intro B hB
    rw [mulVec_smul]
    congr 1
    change P B *ᵥ (Ps.prod *ᵥ x) = Ps.prod *ᵥ x
    rw [mulVec_mulVec, Matrix.mul_list_prod_of_mem (hPs (P B) (List.mem_map_of_mem
      (Finset.mem_toList.mpr hB))).2 Ps (List.mem_map_of_mem (Finset.mem_toList.mpr hB))
      (fun Q hQ => hcPs _ (List.mem_map_of_mem (Finset.mem_toList.mpr hB)) Q hQ)]
  · have hyx : star y ⬝ᵥ x = star y ⬝ᵥ y := Matrix.star_mulVec_dotProduct_of_idem hPih hPiPi x
    rw [star_smul, smul_dotProduct, hyx, Matrix.star_dotProduct_self_eq_re y, ← hrr,
      Complex.star_def, Complex.conj_ofReal, smul_eq_mul, norm_mul, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr),
      abs_of_pos (mul_pos hr hr), mul_pow]
    field_simp
    nlinarith [hy, hrr]

/-! ### D8.19 Actual cutoffs -/

omit [Fintype σ] in
theorem card_subConfig_physReg (d : ℕ) (Δ : Finset σ) :
    Fintype.card (TensorPower.SubConfig (fun f => Fin (dims n d f)) (physReg Δ)) = dimReg n Δ := by
  rw [← Fintype.card_congr (regPhys (n := n) d Δ), Fintype.card_pi]
  simp [dimReg, Finset.prod_attach]

/-- A Specht dimension occurring on `Δ^{⊗k}` is at most `(dim 𝓗_Δ)^k`. -/
theorem dim_le_dimReg_pow (d k : ℕ) {Δ : Finset σ} {μ : IrrepLabel (Equiv.Perm (Fin k))}
    (hμ : Replicas.π (fun f => Fin (dims n d f)) k (physReg Δ) μ ≠ 0) :
    μ.dim ≤ dimReg n Δ ^ k := by
  have h := TensorPower.labelProj_copyPerm_ne_zero_of_subsystemPerm _ k _ hμ
  have := labelDim_le_card _ h
  rw [Fintype.card_fun, card_subConfig_physReg] at this
  simpa using this

/-- D8.19 (`comparator:actual-cutoffs`). For matched `(B, Q)` (`Q ⊆ B` or `B ⊆ Q`,
`Δ = B △ Q`): the labels of `B` and `Q` commute, `F_Q ≤ F_B + k log dim 𝓗_Δ` on their joint
eigenspaces, so the range `{F_B ≤ c}` lies in the range `{F_Q ≤ c + k log dim 𝓗_Δ}`. -/
theorem step_8_19 [∀ v, NeZero (n v)] (d k : ℕ) [NeZero d] {B Q Δ : Finset σ}
    (hBQ : (Q ⊆ B ∧ Δ = B \ Q) ∨ (B ⊆ Q ∧ Δ = Q \ B)) :
    (∀ l l' : IrrepLabel (Equiv.Perm (Fin k)),
      Commute (Replicas.π (fun f => Fin (dims n d f)) k (physReg Q) l)
        (Replicas.π (fun f => Fin (dims n d f)) k (physReg B) l')) ∧
    (∀ l l' : IrrepLabel (Equiv.Perm (Fin k)),
      Replicas.π (fun f => Fin (dims n d f)) k (physReg Q) l *
          Replicas.π (fun f => Fin (dims n d f)) k (physReg B) l' ≠ 0 →
        Real.log l.dim ≤ Real.log l'.dim + k * Real.log (dimReg n Δ)) ∧
    ∀ (c : ℝ) (φ : Transport.Config (dims n d) k → ℂ), cutProj d k B c *ᵥ φ = φ →
      ∀ l : IrrepLabel (Equiv.Perm (Fin k)), c + k * Real.log (dimReg n Δ) < Real.log l.dim →
        Replicas.π (fun f => Fin (dims n d f)) k (physReg Q) l *ᵥ φ = 0 := by
  set ι := fun f : Site σ => Fin (dims n d f)
  have hcomm : ∀ l l' : IrrepLabel (Equiv.Perm (Fin k)),
      Commute (Replicas.π ι k (physReg Q) l) (Replicas.π ι k (physReg B) l') := fun l l' => by
    rcases hBQ with ⟨h, -⟩ | ⟨h, -⟩
    · exact Replicas.step_6_4_8 ι k (Or.inl (physReg_subset h)) l l'
    · exact (Replicas.step_6_4_8 ι k (Or.inl (physReg_subset h)) l' l).symm
  have hD : (0 : ℝ) < dimReg n Δ := by
    rw [← card_subConfig_physReg d]; exact_mod_cast Fintype.card_pos
  -- D8.19.1: `d_λ ≤ d_ν d_μ ≤ d_ν (dim 𝓗_Δ)^k`
  have hdim : ∀ l l' : IrrepLabel (Equiv.Perm (Fin k)),
      Replicas.π ι k (physReg Q) l * Replicas.π ι k (physReg B) l' ≠ 0 →
        l.dim ≤ l'.dim * dimReg n Δ ^ k := fun l l' h => by
    rcases hBQ with ⟨hQB, rfl⟩ | ⟨hBQ, rfl⟩
    · have hU : physReg Q ∪ physReg (B \ Q) = physReg B := by
        rw [physReg, physReg, physReg, ← Finset.map_union, Finset.union_sdiff_of_subset hQB]
      have hdisj : Disjoint (physReg Q) (physReg (B \ Q)) :=
        disjoint_physReg Finset.disjoint_sdiff
      obtain ⟨μ, hμ⟩ := Matrix.exists_mul_mul_ne_zero_of_sum_eq_one _ _
        (Replicas.π ι k (physReg (B \ Q)))
        (sum_labelProj _) h
      rw [← hU] at hμ
      have h1 := (Replicas.lemma_6_1_3 ι k).1 _ _ hdisj l μ l' hμ
      have h2 := dim_le_dimReg_pow d k (Δ := B \ Q) (μ := μ) fun h0 =>
        hμ (by rw [h0, mul_zero, zero_mul])
      calc l.dim ≤ l'.dim * μ.dim := h1.2
        _ ≤ l'.dim * dimReg n (B \ Q) ^ k := Nat.mul_le_mul_left _ h2
    · have hU : physReg B ∪ physReg (Q \ B) = physReg Q := by
        rw [physReg, physReg, physReg, ← Finset.map_union, Finset.union_sdiff_of_subset hBQ]
      have hdisj : Disjoint (physReg B) (physReg (Q \ B)) :=
        disjoint_physReg Finset.disjoint_sdiff
      rw [(hcomm l l').eq] at h
      obtain ⟨μ, hμ⟩ := Matrix.exists_mul_mul_ne_zero_of_sum_eq_one _ _
        (Replicas.π ι k (physReg (Q \ B)))
        (sum_labelProj _) h
      rw [← hU] at hμ
      have h1 := (Replicas.lemma_6_1_3 ι k).1 _ _ hdisj l' μ l hμ
      have h2 := dim_le_dimReg_pow d k (Δ := Q \ B) (μ := μ) fun h0 =>
        hμ (by rw [h0, mul_zero, zero_mul])
      calc l.dim ≤ l'.dim * μ.dim := h1.1
        _ ≤ l'.dim * dimReg n (Q \ B) ^ k := Nat.mul_le_mul_left _ h2
  have hlog : ∀ l l' : IrrepLabel (Equiv.Perm (Fin k)),
      Replicas.π ι k (physReg Q) l * Replicas.π ι k (physReg B) l' ≠ 0 →
        Real.log l.dim ≤ Real.log l'.dim + k * Real.log (dimReg n Δ) := fun l l' h => by
    have h1 := hdim l l' h
    have hl' : (0 : ℝ) < l'.dim := by exact_mod_cast l'.dim_pos
    rw [← Real.log_pow, ← Real.log_mul hl'.ne' (pow_pos hD k).ne']
    exact Real.log_le_log (by exact_mod_cast l.dim_pos) (by exact_mod_cast h1)
  refine ⟨hcomm, hlog, fun c φ hφ l hl => ?_⟩
  -- D8.19.2: `φ` lies in the joint eigenspaces with `F_B ≤ c`
  rw [← hφ, mulVec_mulVec, cutProj, labelObservable, Finset.mul_sum, sum_mulVec]
  refine Finset.sum_eq_zero fun l' _ => ?_
  rw [mul_smul_comm]
  split_ifs with hl'
  · have h0 : Replicas.π ι k (physReg Q) l * Replicas.π ι k (physReg B) l' = 0 := by
      by_contra h0
      have := hlog l l' h0
      linarith
    rw [show Replicas.π ι k (physReg Q) l * labelProj (Replicas.copyPerm ι k (physReg B)) l' =
      0 from h0, smul_zero, zero_mulVec]
  · simp

/-! ### D8.20 The rough upper bound -/

omit [Fintype σ] in
theorem Upper.isPartition_part [Fintype σ] {K : ℕ} {St : Type v} (Γ : Statuses σ K St X)
    (s : St) (g : Fin K) : (Γ.part s g).IsPartition := by
  have hXUY : Disjoint (X ∪ Γ.U s g) (Γ.Y s g) :=
    Finset.disjoint_union_left.mpr ⟨Γ.disjoint_XY s g, Γ.disjoint_UY s g⟩
  have hXUV : Disjoint (X ∪ Γ.U s g) (Γ.V s g) :=
    Finset.disjoint_union_left.mpr ⟨Γ.disjoint_XV s g, Γ.disjoint_UV s g⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Statuses.part, Statuses.P, Statuses.Yr]
    rw [Finset.disjoint_insert_left]
    exact ⟨Upper.C_not_mem_physReg _, disjoint_physReg hXUY⟩
  · simp only [Statuses.part, Statuses.P, Statuses.F]
    rw [Finset.disjoint_insert_left, Finset.disjoint_insert_right]
    exact ⟨by simp [Upper.C_not_mem_physReg], Upper.R_not_mem_physReg _, disjoint_physReg hXUV⟩
  · simp only [Statuses.part, Statuses.Yr, Statuses.F]
    rw [Finset.disjoint_insert_right]
    exact ⟨Upper.R_not_mem_physReg _, disjoint_physReg (Γ.disjoint_YV s g)⟩
  · ext f
    simp only [Statuses.part, Statuses.P, Statuses.Yr, Statuses.F, Finset.mem_union,
      Finset.mem_insert, Finset.mem_univ, iff_true]
    rcases f with v | _ | _
    · have hv : v ∈ X ∪ Γ.U s g ∪ Γ.Y s g ∪ Γ.V s g := by rw [Γ.cover s g]; exact Finset.mem_univ v
      simp only [Finset.mem_union] at hv
      simp only [Upper.phys_mem_physReg, Finset.mem_union, reduceCtorEq, false_or]
      tauto
    · simp
    · simp

variable [∀ v, NeZero (n v)]

theorem posDef_bandA {K : ℕ} {St : Type v} (Γ : Statuses σ K St X) (d : ℕ) [NeZero d] {t : ℝ}
    (ht : 0 ≤ t) (k : ℕ) (s : St) (g : Fin K) : (Γ.bandA n d t k s g).PosDef :=
  Transport.posDef_bandMetric (Upper.isPartition_part Γ s g) ht k

theorem posDef_leafA (h1 : Step_8_1.{u, v}) {K : ℕ} {St : Type v} (Γ : Statuses σ K St X)
    (d : ℕ) [NeZero d] {t : ℝ} (ht : 0 ≤ t) (k : ℕ) (s : St) : (Γ.leafA n d t k s).PosDef :=
  PosDef.listProd_ofFn (fun g => posDef_bandA Γ d ht k s g)
    (fun g g' h => (h1 Γ).2 n d t ht k s s g g' h)

/-- D6.6 labelwise: `(k + 2)^{-C} d_λ^{-t} ≤ w_k(λ) ≤ (k + 2)^C d_λ^{-t}` for occurring labels. -/
theorem exists_w_bounds {I : Type*} [DecidableEq I] [Fintype I] (ι : I → Type*)
    [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)] [∀ f, Nonempty (ι f)] {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, ∀ (k : ℕ) (Q : Finset I) (l : IrrepLabel (Equiv.Perm (Fin k))),
      Replicas.π ι k Q l ≠ 0 →
        ((k : ℝ) + 2) ^ (-C) * Real.exp (-t * Real.log l.dim) ≤ Replicas.w ι t l ∧
          Replicas.w ι t l ≤ ((k : ℝ) + 2) ^ C * Real.exp (-t * Real.log l.dim) := by
  obtain ⟨C, hC⟩ := Replicas.lemma_6_2_2 ι ht
  refine ⟨C, fun k Q l hl => ?_⟩
  obtain ⟨y, hy⟩ : ∃ y, Replicas.π ι k Q l *ᵥ Pi.single y 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hl
    ext a b
    have := congrFun (h b) a
    simpa [mulVec_single_one] using this
  set v := Replicas.π ι k Q l *ᵥ Pi.single y 1
  have hvpos : 0 < (star v ⬝ᵥ v).re := by
    have := (dotProduct_star_self_pos_iff (v := v)).mpr hy
    exact (Complex.pos_iff.mp this).1
  have hlab : ∀ f : IrrepLabel (Equiv.Perm (Fin k)) → ℝ,
      (star v ⬝ᵥ (labelObservable (Replicas.copyPerm ι k Q) f *ᵥ v)).re =
        f l * (star v ⬝ᵥ v).re := fun f => by
    have : labelObservable (Replicas.copyPerm ι k Q) f *ᵥ v = (f l : ℂ) • v := by
      simp only [v, mulVec_mulVec, Replicas.π]
      rw [labelObservable_mul_labelProj, smul_mulVec]
    rw [this, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
  have hE : cfc (fun x => Real.exp (-t * x)) (Replicas.F ι k Q) =
      labelObservable (Replicas.copyPerm ι k Q) fun l => Real.exp (-t * Real.log l.dim) := by
    rw [Replicas.F, cfc_labelObservable]; rfl
  have hW : Replicas.W ι t k Q = labelObservable (Replicas.copyPerm ι k Q)
      fun l => Replicas.w ι t l := rfl
  obtain ⟨h1, h2⟩ := hC k Q
  have q1 := (Matrix.le_iff.mp h1).re_dotProduct_nonneg v
  have q2 := (Matrix.le_iff.mp h2).re_dotProduct_nonneg v
  simp only [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, hE, hW] at q1 q2
  rw [RCLike.re_to_complex] at q1 q2
  simp only [Complex.sub_re, Complex.smul_re, smul_eq_mul, hlab] at q1 q2
  constructor
  · nlinarith
  · nlinarith

/-- No label of `U_{j,g}` or `U_{j,g}Y_{j,g}` (all bands of the leaf `j`) above `c`. -/
def LowCut {K : ℕ} {St : Type v} (Γ : Statuses σ K St X) (d k : ℕ) (s : St) (c : ℝ)
    (v : Transport.Config (dims n d) k → ℂ) : Prop :=
  ∀ g : Fin K, ∀ Q ∈ ({Γ.U s g, Γ.U s g ∪ Γ.Y s g} : Finset (Finset σ)),
    ∀ l : IrrepLabel (Equiv.Perm (Fin k)), c < Real.log l.dim →
      Replicas.π (fun f => Fin (dims n d f)) k (physReg Q) l *ᵥ v = 0

omit [∀ v, NeZero (n v)] in
/-- D8.1 (iii): label functions of the regions `U, UY, Y` of the leaf `j` preserve `LowCut`. -/
theorem lowCut_labelObservable (h1 : Step_8_1.{u, v}) {K : ℕ} {St : Type v}
    (Γ : Statuses σ K St X) (d k : ℕ) (s : St) (c : ℝ) (g' : Fin K) {Q' : Finset σ}
    (hQ' : Q' ∈ ({Γ.U s g', Γ.U s g' ∪ Γ.Y s g', Γ.Y s g'} : Finset (Finset σ)))
    (f : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) {v : Transport.Config (dims n d) k → ℂ}
    (hv : LowCut Γ d k s c v) :
    LowCut Γ d k s c
      (labelObservable (Replicas.copyPerm (fun f => Fin (dims n d f)) k (physReg Q')) f *ᵥ v) := by
  intro g Q hQ l hl
  have hQ3 : Q ∈ ({Γ.U s g, Γ.U s g ∪ Γ.Y s g, Γ.Y s g} : Finset (Finset σ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hQ ⊢
    tauto
  have hnest := (h1 Γ).1 s g g' Q hQ3 Q' hQ'
  have hc : Commute (Replicas.π (fun f => Fin (dims n d f)) k (physReg Q) l)
      (labelObservable (Replicas.copyPerm (fun f => Fin (dims n d f)) k (physReg Q')) f) := by
    rw [Replicas.π, labelProj_eq_labelObservable_ite]
    rcases hnest with h | h | h
    · exact Replicas.commute_labelObservable _ k (Or.inl (physReg_subset h)) _ _
    · exact (Replicas.commute_labelObservable _ k (Or.inl (physReg_subset h)) _ _).symm
    · exact Replicas.commute_labelObservable _ k (Or.inr (disjoint_physReg h)) _ _
  rw [mulVec_mulVec, hc.eq, ← mulVec_mulVec, hv g Q hQ l hl, mulVec_zero]

/-- D8.20.1 (one band): `‖Ã_{j,g} v‖ ≤ ((k + 2)^{3C} e^{2tc})² ‖v‖` on `LowCut` vectors. -/
theorem nsq_Atil_le (h1 : Step_8_1.{u, v}) {K : ℕ} {St : Type v} (Γ : Statuses σ K St X)
    (d : ℕ) [NeZero d] {t C : ℝ} (ht : 0 < t)
    (hC : ∀ (k : ℕ) (Q : Finset (Site σ)) (l : IrrepLabel (Equiv.Perm (Fin k))),
      Replicas.π (fun f => Fin (dims n d f)) k Q l ≠ 0 →
        ((k : ℝ) + 2) ^ (-C) * Real.exp (-t * Real.log l.dim) ≤
          Replicas.w (fun f => Fin (dims n d f)) t l ∧
        Replicas.w (fun f => Fin (dims n d f)) t l ≤
          ((k : ℝ) + 2) ^ C * Real.exp (-t * Real.log l.dim))
    (k : ℕ) (s : St) (c : ℝ) (g : Fin K) {v : Transport.Config (dims n d) k → ℂ}
    (hv : LowCut Γ d k s c v) :
    (star (Γ.Atil n d t k s g *ᵥ v) ⬝ᵥ (Γ.Atil n d t k s g *ᵥ v)).re ≤
        (((((k : ℝ) + 2) ^ C * Real.exp (t * c)) ^ 2 * ((k : ℝ) + 2) ^ C) ^ 2) ^ 2 *
          (star v ⬝ᵥ v).re ∧
      LowCut Γ d k s c (Γ.Atil n d t k s g *ᵥ v) := by
  set ι := fun f : Site σ => Fin (dims n d f)
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hw : ∀ l : IrrepLabel (Equiv.Perm (Fin k)), 0 < Replicas.w ι t l := fun l =>
    TensorPower.replicaLabelWeight_pos ι ht.le l
  set M₀ := ((k : ℝ) + 2) ^ C
  set M₁ := ((k : ℝ) + 2) ^ C * Real.exp (t * c)
  have hM₀ : 0 ≤ M₀ := by positivity
  have hM₁ : 0 ≤ M₁ := by positivity
  -- the three factors on `LowCut` vectors
  have hY : ∀ v, LowCut Γ d k s c v →
      (star (Replicas.W ι t k (physReg (Γ.Y s g)) *ᵥ v) ⬝ᵥ
          (Replicas.W ι t k (physReg (Γ.Y s g)) *ᵥ v)).re ≤ M₀ ^ 2 * (star v ⬝ᵥ v).re ∧
        LowCut Γ d k s c (Replicas.W ι t k (physReg (Γ.Y s g)) *ᵥ v) := fun v hv => by
    refine ⟨re_dotProduct_labelObservable_mulVec_le _ v fun l hl => ?_,
      lowCut_labelObservable h1 Γ d k s c g (by simp) _ hv⟩
    have hπ : Replicas.π ι k (physReg (Γ.Y s g)) l ≠ 0 := fun h0 => hl (by
      rw [show labelProj _ l = Replicas.π ι k (physReg (Γ.Y s g)) l from rfl, h0, zero_mulVec])
    rw [abs_of_pos (hw l)]
    refine (hC k _ l hπ).2.trans ?_
    have : Real.exp (-t * Real.log l.dim) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have := Real.log_nonneg (by exact_mod_cast l.dim_pos : (1 : ℝ) ≤ l.dim)
      nlinarith)
    calc _ ≤ ((k : ℝ) + 2) ^ C * 1 := mul_le_mul_of_nonneg_left this (by positivity)
      _ = M₀ := mul_one _
  have hInv : ∀ Q ∈ ({Γ.U s g, Γ.U s g ∪ Γ.Y s g} : Finset (Finset σ)), ∀ v,
      LowCut Γ d k s c v →
      (star ((Replicas.W ι t k (physReg Q))⁻¹ *ᵥ v) ⬝ᵥ
          ((Replicas.W ι t k (physReg Q))⁻¹ *ᵥ v)).re ≤ M₁ ^ 2 * (star v ⬝ᵥ v).re ∧
        LowCut Γ d k s c ((Replicas.W ι t k (physReg Q))⁻¹ *ᵥ v) := fun Q hQ v hv => by
    rw [Replicas.W_inv ι ht.le]
    have hQ' : Q ∈ ({Γ.U s g, Γ.U s g ∪ Γ.Y s g, Γ.Y s g} : Finset (Finset σ)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hQ ⊢
      tauto
    refine ⟨re_dotProduct_labelObservable_mulVec_le _ v fun l hl => ?_,
      lowCut_labelObservable h1 Γ d k s c g hQ' _ hv⟩
    have hπ : Replicas.π ι k (physReg Q) l ≠ 0 := fun h0 => hl (by
      rw [show labelProj _ l = Replicas.π ι k (physReg Q) l from rfl, h0, zero_mulVec])
    have hlc : Real.log l.dim ≤ c := by
      by_contra hlc
      exact hl (hv g Q hQ l (lt_of_not_ge hlc))
    rw [abs_of_pos (inv_pos.mpr (hw l))]
    have hlow := (hC k _ l hπ).1
    have hpos : 0 < ((k : ℝ) + 2) ^ (-C) * Real.exp (-t * Real.log l.dim) := by positivity
    calc (Replicas.w ι t l)⁻¹ ≤ (((k : ℝ) + 2) ^ (-C) * Real.exp (-t * Real.log l.dim))⁻¹ :=
          inv_anti₀ hpos hlow
      _ = ((k : ℝ) + 2) ^ C * Real.exp (t * Real.log l.dim) := by
          rw [mul_inv, ← Real.rpow_neg hk2.le, neg_neg, ← Real.exp_neg]
          ring_nf
      _ ≤ M₁ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left hlc ht.le)) (by positivity)
  -- `X = W_U^{-1} W_{UY}^{-1} W_Y`
  have hX : ∀ v, LowCut Γ d k s c v →
      (star (((Replicas.W ι t k (physReg (Γ.U s g)))⁻¹ *
          (Replicas.W ι t k (physReg (Γ.U s g ∪ Γ.Y s g)))⁻¹ *
          Replicas.W ι t k (physReg (Γ.Y s g))) *ᵥ v) ⬝ᵥ
        (((Replicas.W ι t k (physReg (Γ.U s g)))⁻¹ *
          (Replicas.W ι t k (physReg (Γ.U s g ∪ Γ.Y s g)))⁻¹ *
          Replicas.W ι t k (physReg (Γ.Y s g))) *ᵥ v)).re ≤
        (M₁ ^ 2 * M₀) ^ 2 * (star v ⬝ᵥ v).re ∧
      LowCut Γ d k s c (((Replicas.W ι t k (physReg (Γ.U s g)))⁻¹ *
          (Replicas.W ι t k (physReg (Γ.U s g ∪ Γ.Y s g)))⁻¹ *
          Replicas.W ι t k (physReg (Γ.Y s g))) *ᵥ v) := fun v hv => by
    obtain ⟨a1, b1⟩ := hY v hv
    obtain ⟨a2, b2⟩ := hInv (Γ.U s g ∪ Γ.Y s g) (by simp) _ b1
    obtain ⟨a3, b3⟩ := hInv (Γ.U s g) (by simp) _ b2
    rw [← mulVec_mulVec, ← mulVec_mulVec]
    refine ⟨?_, b3⟩
    calc _ ≤ M₁ ^ 2 * (M₁ ^ 2 * (M₀ ^ 2 * (star v ⬝ᵥ v).re)) :=
          a3.trans (mul_le_mul_of_nonneg_left (a2.trans (mul_le_mul_of_nonneg_left a1
            (sq_nonneg _))) (sq_nonneg _))
      _ = _ := by ring
  obtain ⟨c1, d1⟩ := hX v hv
  obtain ⟨c2, d2⟩ := hX _ d1
  rw [Statuses.Atil, pow_two, ← mulVec_mulVec]
  refine ⟨?_, d2⟩
  calc _ ≤ (M₁ ^ 2 * M₀) ^ 2 * ((M₁ ^ 2 * M₀) ^ 2 * (star v ⬝ᵥ v).re) :=
        c2.trans (mul_le_mul_of_nonneg_left c1 (sq_nonneg _))
    _ = _ := by ring

/-- D8.20.1: on pinned symmetric `LowCut` vectors, `A_j φ = ∏_g Ã_{j,g} φ` (D8.16) and
`⟨φ, A_j φ⟩ ≤ M^K`, `M = ((k + 2)^{3C} e^{2tc})²` (D6.6, all labels of a leaf commute). -/
theorem leaf_bound (h1 : Step_8_1.{u, v}) (h16 : Step_8_16.{u, v}) (E : TypicalSet D X)
    {K : ℕ} {St : Type v} (Γ : Statuses σ K St X) {t C : ℝ} (ht : 0 < t)
    (hC : ∀ (k : ℕ) (Q : Finset (Site σ)) (l : IrrepLabel (Equiv.Perm (Fin k))),
      Replicas.π (fun f => Fin (dims n E.d f)) k Q l ≠ 0 →
        ((k : ℝ) + 2) ^ (-C) * Real.exp (-t * Real.log l.dim) ≤
          Replicas.w (fun f => Fin (dims n E.d f)) t l ∧
        Replicas.w (fun f => Fin (dims n E.d f)) t l ≤
          ((k : ℝ) + 2) ^ C * Real.exp (-t * Real.log l.dim))
    (k : ℕ) (s : St) (c : ℝ) {φ : Transport.Config (dims n E.d) k → ℂ}
    (hφ1 : star φ ⬝ᵥ φ = 1) (hS : φ ∈ Replicas.S (fun f => Fin (dims n E.d f)) k)
    (hP : pinProj E k *ᵥ φ = φ) (hcut : LowCut Γ E.d k s c φ) :
    (star φ ⬝ᵥ (Γ.leafA n E.d t k s *ᵥ φ)).re ≤
      (((((k : ℝ) + 2) ^ C * Real.exp (t * c)) ^ 2 * ((k : ℝ) + 2) ^ C) ^ 2) ^ K := by
  set M := ((((k : ℝ) + 2) ^ C * Real.exp (t * c)) ^ 2 * ((k : ℝ) + 2) ^ C) ^ 2
  have hM : 0 ≤ M := sq_nonneg _
  have h16' := fun g => (h16 E Γ).1 t ht.le k s g
  -- D8.16: `A_{j,g} = Ã_{j,g}` on the pinned symmetric range, band by band
  have heq := (Matrix.listProd_ofFn_mulVec_eq (fun g => Γ.bandA n E.d t k s g)
    (fun g => Γ.Atil n E.d t k s g)
    (fun φ => φ ∈ Replicas.S (fun f => Fin (dims n E.d f)) k ∧ pinProj E k *ᵥ φ = φ)
    (fun g φ hφ => ((h16' g).1 φ hφ.1 hφ.2).1)
    (fun g φ hφ => ⟨((h16' g).1 φ hφ.1 hφ.2).2.1, ((h16' g).1 φ hφ.1 hφ.2).2.2⟩) φ ⟨hS, hP⟩).1
  -- D8.20.1: `‖∏_g Ã_{j,g} φ‖ ≤ M^K`
  have hn := (Matrix.listProd_ofFn_nsq_le (fun g => Γ.Atil n E.d t k s g) (LowCut Γ E.d k s c)
    (fun g v hv => (nsq_Atil_le h1 Γ E.d ht hC k s c g hv).2)
    (fun g v hv => (nsq_Atil_le h1 Γ E.d ht hC k s c g hv).1) φ hcut).1
  rw [hφ1, Complex.one_re, mul_one] at hn
  rw [Statuses.leafA, heq]
  have hcs := norm_star_dotProduct_sq_le φ ((List.ofFn fun g => Γ.Atil n E.d t k s g).prod *ᵥ φ)
  rw [hφ1, Complex.one_re, one_mul] at hcs
  have h2 : ‖star φ ⬝ᵥ ((List.ofFn fun g => Γ.Atil n E.d t k s g).prod *ᵥ φ)‖ ≤ M ^ K :=
    le_of_sq_le_sq (hcs.trans hn) (pow_nonneg hM K)
  exact (Complex.re_le_norm _).trans h2

/-- D8.20.2–D8.20.4 with D8.15: for a unit `φ` with `⟨φ, A_j φ⟩ ≤ L` at every leaf,
`(z/d_*²)^k |⟨φ, π^λ_R post_k⟩|² ≤ √L N²`. -/
theorem rough_core (h1 : Step_8_1.{u, v}) (h15 : Step_8_15.{u, v}) (E : TypicalSet D X)
    {K : ℕ} {St : Type v} [Finite St] (Γ : Statuses σ K St X) (T : Transport.MeanTree St)
    {a : ℝ} (ha : 0 ≤ a) (k : ℕ) (l : IrrepLabel (Equiv.Perm (Fin k)))
    {φ : Transport.Config (dims n E.d) k → ℂ} (hφ1 : star φ ⬝ᵥ φ = 1) {L : ℝ} (hL : 0 < L)
    (hφL : ∀ s, (star φ ⬝ᵥ (Γ.leafA n E.d (a / 2) k s *ᵥ φ)).re ≤ L) :
    (E.z / E.d ^ 2) ^ k * ‖star φ ⬝ᵥ (piR E.d k l *ᵥ post E k)‖ ^ 2 ≤
      Real.sqrt L * N2 D Γ E T a k l := by
  classical
  have := Fintype.ofFinite St
  have hA : ∀ s, (Γ.leafA n E.d (a / 2) k s).PosDef :=
    fun s => posDef_leafA h1 Γ E.d (by linarith) k s
  set M := Γ.root n E.d T (a / 2) k
  have hM : M.PosDef := Transport.MeanTree.posDef_eval hA T
  have hq : ∀ s, 0 ≤ (star φ ⬝ᵥ (Γ.leafA n E.d (a / 2) k s *ᵥ φ)).re :=
    fun s => (hA s).posSemidef.re_dotProduct_nonneg φ
  -- D8.20.2: vector Jensen through the tree
  have hJ : (star φ ⬝ᵥ (M *ᵥ φ)).re ≤ L := by
    refine (Transport.lemma_7_1_4 hA T φ).trans ?_
    calc ∏ s, (star φ ⬝ᵥ (Γ.leafA n E.d (a / 2) k s *ᵥ φ)).re ^ T.weight s ≤
          ∏ s, L ^ T.weight s :=
          Finset.prod_le_prod (fun s _ => Real.rpow_nonneg (hq s) _)
            (fun s _ => Real.rpow_le_rpow (hq s) (hφL s) (T.weight_nonneg s))
      _ = L := by rw [← Real.rpow_sum_of_pos hL, T.sum_weight, Real.rpow_one]
  -- D8.20.3: scalar Jensen (concavity of `x^{2s}`, `2s = 1/2`)
  have hJ2 : (star φ ⬝ᵥ (M ^ (2 * (1 / 4 : ℝ)) *ᵥ φ)).re ≤ Real.sqrt L := by
    have h := re_dotProduct_rpow_mulVec_le hM.posSemidef (p := 2 * (1 / 4))
      ⟨by norm_num, by norm_num⟩ φ
    rw [hφ1, Complex.one_re, Real.one_rpow, one_mul] at h
    refine h.trans ?_
    rw [Real.sqrt_eq_rpow, show (2 * (1 / 4) : ℝ) = 1 / 2 by norm_num]
    exact Real.rpow_le_rpow (hM.posSemidef.re_dotProduct_nonneg φ) hJ (by norm_num)
  -- D8.20.4: Cauchy–Schwarz with opposite powers
  have hCS := hM.norm_star_dotProduct_sq_le_rpow (1 / 4) φ (piR E.d k l *ᵥ post E k)
  have hf0 : 0 ≤ Matrix.Transport.filteredNormSq M (piR E.d k l *ᵥ post E k) :=
    (Complex.nonneg_iff.mp (dotProduct_star_self_nonneg _)).1
  have hz : 0 ≤ (E.z / E.d ^ 2) ^ k := by have := E.z_pos; positivity
  -- D8.15
  have h15' := h15 D E Γ T a ha k l
  calc (E.z / E.d ^ 2) ^ k * ‖star φ ⬝ᵥ (piR E.d k l *ᵥ post E k)‖ ^ 2 ≤
        (E.z / E.d ^ 2) ^ k * (Real.sqrt L *
          Matrix.Transport.filteredNormSq M (piR E.d k l *ᵥ post E k)) :=
        mul_le_mul_of_nonneg_left (hCS.trans (mul_le_mul_of_nonneg_right hJ2 hf0)) hz
    _ = Real.sqrt L * ((E.z / E.d ^ 2) ^ k *
          Matrix.Transport.filteredNormSq M (piR E.d k l *ᵥ post E k)) := by ring
    _ ≤ Real.sqrt L * N2 D Γ E T a k l := mul_le_mul_of_nonneg_left h15' (Real.sqrt_nonneg _)

end Rough

/-- D8.20 (`comparator:rough-upper`). (comparator:rough-upper) of D8.8. -/
theorem step_8_20 (h1 : Step_8_1.{u, v}) (h10 : Step_8_10.{u}) (h11 : Step_8_11.{u})
    (h15 : Step_8_15.{u, v}) (h16 : Step_8_16.{u, v}) : Step_8_20.{u, v} := by
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro σ _ _ n _ D X E K St _ _ Γ l hl 𝓡 Bsh Bexc h𝓡 a ha ha₀
  set cs := Bsh / E.z + Bexc
  have hz := E.z_pos
  have hd : (0 : ℝ) < E.d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne E.d)
  have ht : 0 < a / 2 := by linarith
  obtain ⟨C, hC⟩ := exists_w_bounds (fun f : Site σ => Fin (dims n E.d f)) ht
  -- D8.18
  obtain ⟨c, N, hc, k₀, hφ⟩ := step_8_18 h10 h11 E hl 𝓡 h𝓡.nested h𝓡.disjoint
  obtain ⟨c', N', hc', ε', -, hq⟩ := hl
  obtain ⟨base, hbase⟩ : ∃ b : ℝ, b = 2 * Real.log E.d - Real.log E.z +
      2 * (1 / 4) * (a * K) * (2 * Bsh / E.z + 2 * Bexc) := ⟨_, rfl⟩
  simp only [RoughUpper]
  rw [← hbase]
  set Gm : ℕ → ℝ := fun k =>
    -Real.log c + N * Real.log ((k : ℝ) + 1) + 3 * C * K * Real.log ((k : ℝ) + 2)
  set Lc : ℕ → ℝ := fun k => 1 + ∑ s, ∑ y, ∑ y', ‖Γ.leafA n E.d (a / 2) k s y y'‖
  set Gc : ℕ → ℝ := fun k => Real.log (Real.sqrt (Lc k)) -
    Real.log ((E.z / E.d ^ 2) ^ k * q E k (l k)) - k * base
  set G : ℕ → ℝ := fun k => if k₀ ≤ k then Gm k else Gc k
  have hmain : ∀ (k : ℕ) (T : Transport.MeanTree St),
      -Real.log (N2 D Γ E T a k (l k)) ≤ k * base + G k := by
    intro k T
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    by_cases hk : k₀ ≤ k
    · simp only [G, if_pos hk]
      obtain ⟨φ, hφ1, hS, hP, hcutB, hov⟩ := hφ k hk
      -- D8.19: every vector of the common range lies in `{F_Q ≤ k(B_sh/z + B_exc)}`
      have hcut : ∀ s, LowCut Γ E.d k s (k * cs) φ := by
        intro s g Q hQ l' hl'
        obtain ⟨B, hB, hm⟩ := h𝓡.matched s g Q hQ
        have key : ∀ Δ, ((Q ⊆ B ∧ Δ = B \ Q) ∨ (B ⊆ Q ∧ Δ = Q \ B)) →
            1 + Real.log (dimReg n Δ) ≤ Bexc →
            Replicas.π (fun f => Fin (dims n E.d f)) k (physReg Q) l' *ᵥ φ = 0 := by
          intro Δ hΔ hb
          refine (step_8_19 E.d k hΔ).2.2 _ φ (hcutB B hB) l' ?_
          have hSB : D.S B / E.z ≤ Bsh / E.z :=
            div_le_div_of_nonneg_right (h𝓡.entropy_le B hB) hz.le
          have : (k : ℝ) * (D.S B / E.z + 1) + k * Real.log (dimReg n Δ) ≤ k * cs := by
            rw [← mul_add]
            exact mul_le_mul_of_nonneg_left (by simp only [cs]; linarith) hk0
          linarith
        rcases hm with ⟨hQB, hb⟩ | ⟨hBQ, hb⟩
        · exact key (B \ Q) (Or.inl ⟨hQB, rfl⟩) hb
        · exact key (Q \ B) (Or.inr ⟨hBQ, rfl⟩) hb
      -- D8.20.1
      set A := ((k : ℝ) + 2) ^ C * Real.exp (a / 2 * (k * cs))
      set Y := (A ^ 2 * ((k : ℝ) + 2) ^ C) ^ K
      have hY0 : 0 < Y := by positivity
      have hleaf : ∀ s, (star φ ⬝ᵥ (Γ.leafA n E.d (a / 2) k s *ᵥ φ)).re ≤ Y ^ 2 := by
        intro s
        refine (leaf_bound h1 h16 E Γ ht hC k s (k * cs) hφ1 hS hP (hcut s)).trans
          (le_of_eq ?_)
        simp only [Y, A]
        rw [← pow_mul, ← pow_mul, mul_comm 2 K]
      -- D8.20.2–D8.20.4 and D8.15
      have hcore := rough_core h1 h15 E Γ T ha.le k (l k) hφ1 (pow_pos hY0 2) hleaf
      rw [Real.sqrt_sq hY0.le] at hcore
      -- D8.20.5: take `-log`
      set P := (E.z / E.d ^ 2) ^ k * (c * ((k : ℝ) + 1) ^ (-N))
      have hP0 : 0 < P := by positivity
      have hPN : P ≤ Y * N2 D Γ E T a k (l k) :=
        le_trans (mul_le_mul_of_nonneg_left hov (by positivity)) hcore
      have hN0 : 0 < N2 D Γ E T a k (l k) := by
        by_contra h
        have : Y * N2 D Γ E T a k (l k) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hY0.le (not_lt.mp h)
        linarith
      have hlog := Real.log_le_log hP0 hPN
      rw [Real.log_mul hY0.ne' hN0.ne'] at hlog
      have hlogP : Real.log P = k * (Real.log E.z - 2 * Real.log E.d) + Real.log c -
          N * Real.log ((k : ℝ) + 1) := by
        simp only [P]
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
          Real.log_div hz.ne' (by positivity), Real.log_pow,
          Real.log_mul hc.ne' (by positivity), Real.log_rpow (by positivity)]
        push_cast
        ring
      have hlogY : Real.log Y = K * (3 * C * Real.log ((k : ℝ) + 2) + a * (k * cs)) := by
        simp only [Y, A]
        rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow,
          Real.log_mul (by positivity) (by positivity), Real.log_rpow (by positivity),
          Real.log_exp]
        push_cast
        ring
      have hid : k * base + Gm k = Real.log Y - Real.log P := by
        rw [hlogY, hlogP, hbase]
        simp only [Gm, cs]
        field_simp
        ring
      linarith
    · simp only [G, if_neg hk]
      -- the finitely many small `k`: `φ = π_R post / ‖π_R post‖`
      set x := piR E.d k (l k) *ᵥ post E k
      have hq0 : 0 < (star x ⬝ᵥ x).re := lt_of_lt_of_le (by positivity) (hq k).1
      obtain ⟨hφ1, hov⟩ := Matrix.normalize_spec x hq0
      have hLc : 0 < Lc k := by simp only [Lc]; positivity
      have hleaf : ∀ s, (star ((((Real.sqrt (star x ⬝ᵥ x).re)⁻¹ : ℝ) : ℂ) • x) ⬝ᵥ
          (Γ.leafA n E.d (a / 2) k s *ᵥ ((((Real.sqrt (star x ⬝ᵥ x).re)⁻¹ : ℝ) : ℂ) • x))).re ≤
            Lc k := fun s => by
        refine (Matrix.re_dotProduct_mulVec_le_sum_norm _ hφ1).trans ?_
        simp only [Lc]
        have := Finset.single_le_sum (f := fun s => ∑ y, ∑ y', ‖Γ.leafA n E.d (a / 2) k s y y'‖)
          (fun s _ => Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun y' _ => norm_nonneg _)
          (Finset.mem_univ s)
        linarith
      have hcore := rough_core h1 h15 E Γ T ha.le k (l k) hφ1 hLc hleaf
      rw [hov] at hcore
      set P := (E.z / E.d ^ 2) ^ k * q E k (l k)
      have hP0 : 0 < P := mul_pos (by positivity) hq0
      have hs : 0 < Real.sqrt (Lc k) := Real.sqrt_pos.mpr hLc
      have hN0 : 0 < N2 D Γ E T a k (l k) := by
        by_contra h
        have : Real.sqrt (Lc k) * N2 D Γ E T a k (l k) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hs.le (not_lt.mp h)
        have : P ≤ Real.sqrt (Lc k) * N2 D Γ E T a k (l k) := hcore
        linarith
      have hlog := Real.log_le_log hP0 hcore
      rw [Real.log_mul hs.ne' hN0.ne'] at hlog
      simp only [Gc]
      linarith
  refine ⟨fun k => if k = 0 then |base| else G k / k, ?_, fun k _ T => ?_⟩
  · have hev : (fun k : ℕ => Gm k / k) =ᶠ[atTop]
        fun k => if k = 0 then |base| else G k / k := by
      filter_upwards [eventually_ge_atTop (max k₀ 1)] with k hk
      have hk0 : k ≠ 0 := by omega
      have hkk : k₀ ≤ k := le_of_max_le_left hk
      simp only [hk0, if_false, G, if_pos hkk]
    refine Tendsto.congr' hev ?_
    have h := ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (-Real.log c)).add
      (((Real.tendsto_log_natCast_add_div 1).const_mul (N : ℝ)).add
        ((Real.tendsto_log_natCast_add_div 2).const_mul (3 * C * K)))
    simp only [mul_zero, add_zero] at h
    refine h.congr fun k => ?_
    simp only [Gm]
    ring
  · by_cases hk : k = 0
    · subst hk
      simp only [Nat.cast_zero, div_zero, if_true]
      linarith [neg_abs_le base]
    · have hk' : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
      simp only [hk, if_false]
      rw [div_le_iff₀ hk']
      calc -Real.log (N2 D Γ E T a k (l k)) ≤ k * base + G k := hmain k T
        _ = (base + G k / k) * k := by field_simp

end AreaLaw.Comparators
