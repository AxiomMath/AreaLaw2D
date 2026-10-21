import AreaLawRefactored.S08_Comparators.ComponentInverse
import AreaLawRefactored.S08_Comparators.Entropy
import AreaLawRefactored.S06_Replicas.Ported.InverseCompressionLowerPin
import AreaLawForMathlib.Analysis.SpecialFunctions.BinEntropySubsetCount

/-!
# §8.4 Inverse compression and lower pin (D8.31)

Digest `digest/08-comparators.md` D8.31, paper `paper/sections/07-comparators.tex` 577–600.
No geometry.
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix Filter Topology Arealaw Entropy PermutationRepresentation

namespace AreaLaw.Comparators

universe u v

set_option synthInstance.maxSize 256

/-! ## D8.31.4 The lower pin from a compressed inverse -/

section LowerPin

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- D8.31.4. `⟨Px, A^{-1} Px⟩ ≤ c ⟨x, Px⟩` for all `x` gives `c^{-1} P ≤ A`. -/
theorem le_of_compression_le {A P : Matrix N N ℂ} (hA : A.PosDef) (hP : IsStarProjection P)
    {c : ℝ} (hc : 0 < c)
    (h : ∀ x, (star (P *ᵥ x) ⬝ᵥ (A⁻¹ *ᵥ (P *ᵥ x))).re ≤ c * (star x ⬝ᵥ (P *ᵥ x)).re) :
    c⁻¹ • P ≤ A := by
  have hPH : Pᴴ = P := hP.isSelfAdjoint.star_eq
  have hAi : (A⁻¹)ᴴ = A⁻¹ := hA.inv.isHermitian.eq
  refine PosDef.inv_smul_projection_le_of_compression_inv_le hA hP hc ?_
  refine le_of_re_dotProduct_le ?_ ?_ fun x => ?_
  · rw [IsHermitian, conjTranspose_mul, conjTranspose_mul, hPH, hAi, mul_assoc]
  · rw [IsHermitian, conjTranspose_smul, hPH, star_trivial]
  · have e : star x ⬝ᵥ ((P * A⁻¹ * P) *ᵥ x) = star (P *ᵥ x) ⬝ᵥ (A⁻¹ *ᵥ (P *ᵥ x)) := by
      rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec, hPH]
    rw [e, smul_mulVec, dotProduct_smul, Complex.smul_re, smul_eq_mul]
    exact h x

/-- D8.31.4. A lower pin below `Π_k` passes to the band metric `Π_k A + (1 - Π_k)`. -/
theorem le_proj_mul_add_one_sub {A L S : Matrix N N ℂ} {c : ℝ} (hS : IsStarProjection S)
    (hAS : Commute S A) (hLS : S * L = L) (hL : IsSelfAdjoint L) (h : c • L ≤ A) :
    c • L ≤ S * A + (1 - S) := by
  have hSH : IsSelfAdjoint S := hS.isSelfAdjoint
  have hLS' : L * S = L := by
    have := congrArg star hLS
    rwa [star_mul, hL.star_eq, hSH.star_eq] at this
  have h1 : S * (c • L) * S = c • L := by rw [mul_smul_comm, hLS, smul_mul_assoc, hLS']
  have h2 : S * A * S = S * A := by rw [mul_assoc, ← hAS.eq, ← mul_assoc, hS.isIdempotentElem.eq]
  have h3 := hSH.conjugate_le_conjugate h
  rw [h1, h2] at h3
  have h4 : 0 ≤ 1 - S := hS.one_sub.nonneg
  calc c • L ≤ S * A := h3
    _ ≤ S * A + (1 - S) := le_add_of_nonneg_right h4

end LowerPin

/-! ## D8.31.1–D8.31.3 The compressed inverse -/

section Compression

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} [∀ v, NeZero (n v)] (D : PhysData n)
  (d : ℕ) [NeZero d] {K : ℕ} {St : Type v} {X : Finset σ} (Γ : Statuses σ K St X)

omit [∀ v, NeZero (n v)] [NeZero d] in
/-- D8.31.1. `log binom(k, r) ≤ k h(τ)` for `r ≤ τ k`, `0 < τ ≤ 1/2`. -/
theorem log_choose_le {τ : ℝ} (hτ0 : 0 < τ) (hτ : τ ≤ 1 / 2) {k r : ℕ} (hr : (r : ℝ) ≤ τ * k)
    (hrk : r ≤ k) : Real.log (k.choose r) ≤ k * Real.binEntropy τ := by
  have h := choose_le_exp_binEntropy (α := Fin k) hτ0 hτ (r := r) (by simpa using hr)
  simp only [Fintype.card_fin] at h
  rw [Real.log_le_iff_le_exp (by exact_mod_cast Nat.choose_pos hrk)]
  exact h

omit [∀ v, NeZero (n v)] [NeZero d] in
/-- D8.31.1. `#{B : |B| ≤ τ k} ≤ e^{k h(τ)}`. -/
theorem card_filter_le {τ : ℝ} (hτ0 : 0 < τ) (hτ : τ ≤ 1 / 2) (k : ℕ) :
    ((Finset.univ.filter fun B : Finset (Fin k) => (B.card : ℝ) ≤ τ * k).card : ℝ) ≤
      Real.exp (k * Real.binEntropy τ) := by
  simpa using card_filter_card_le_le_exp_binEntropy (α := Fin k) hτ0 hτ

/-- D8.31.2, D8.31.3 (rough). For `x`, `⟨Πx, A_{j,g}^{-1} Πx⟩ ≤ exp{k h(τ) + C log(k + 2)
- 2a log d_{λ_k} + 2a τ k log d_* + 3a k h(τ)} ⟨x, Πx⟩`. -/
theorem compression_rough {a : ℝ} (ha : 0 < a) (ha1 : 2 * a ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 → ∀ (k : ℕ)
      (l : IrrepLabel (Equiv.Perm (Fin k))) (s : St) (g : Fin K)
      (x : Transport.Config (dims n d) k → ℂ),
      (star (lowProj D d τ k l *ᵥ x) ⬝ᵥ ((Replicas.A (fun f => Fin (dims n d f)) (a / 2) k
          (Γ.P s g) (Γ.Yr s g) (Γ.F s g))⁻¹ *ᵥ (lowProj D d τ k l *ᵥ x))).re ≤
        Real.exp (k * Real.binEntropy τ + C * Real.log ((k : ℝ) + 2) - 2 * a * Real.log l.dim +
          2 * a * (τ * k) * Real.log d + 3 * a * (k * Real.binEntropy τ)) *
          (star x ⬝ᵥ (lowProj D d τ k l *ᵥ x)).re := by
  obtain ⟨C, hC, hci⟩ := component_inverse_rough D d Γ ha ha1
  refine ⟨C, hC, fun τ hτ0 hτ k l s g x => ?_⟩
  obtain ⟨hPproj, -⟩ := lowProj_spec D d τ k l
  set P := lowProj D d τ k l
  set u := P *ᵥ x
  have hu : P *ᵥ u = u := by rw [mulVec_mulVec, hPproj.isIdempotentElem.eq]
  obtain ⟨hsum, hnorm, -⟩ := step_8_24 D d τ k l hu
  set F := Finset.univ.filter fun B : Finset (Fin k) => (B.card : ℝ) ≤ τ * k
  set A := Replicas.A (fun f => Fin (dims n d f)) (a / 2) k (Γ.P s g) (Γ.Yr s g) (Γ.F s g)
  have hA : A.PosDef := (Replicas.eq_replicas_leaf_metric (fun f => Fin (dims n d f))
    (by linarith : (0 : ℝ) ≤ a / 2) k (disjoint_P_Yr Γ s g) (disjoint_P_F Γ s g)
    (disjoint_Yr_F Γ s g)).2.2.2.2.1
  set G := Real.exp (C * Real.log ((k : ℝ) + 2) - 2 * a * Real.log l.dim +
    2 * a * (τ * k) * Real.log d + 3 * a * (k * Real.binEntropy τ))
  have hd : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast NeZero.one_le)
  have hh : 0 ≤ Real.binEntropy τ := Real.binEntropy_nonneg hτ0.le (by linarith)
  -- D8.31.3: the bound of D8.30 is uniform over `|B| ≤ τ k`
  have hB : ∀ B ∈ F, (star (compProj D d k B *ᵥ u) ⬝ᵥ (A⁻¹ *ᵥ (compProj D d k B *ᵥ u))).re ≤
      G * (star (compProj D d k B *ᵥ u) ⬝ᵥ (compProj D d k B *ᵥ u)).re := by
    intro B hBF
    have hr : (B.card : ℝ) ≤ τ * k := (Finset.mem_filter.mp hBF).2
    have hrk : B.card ≤ k := (Finset.card_le_univ B).trans (by simp)
    have hlc := log_choose_le hτ0 hτ hr hrk
    refine (hci τ k l u hu B s g).trans (mul_le_mul_of_nonneg_right ?_
      (Complex.nonneg_iff.mp (dotProduct_star_self_nonneg _)).1)
    refine Real.exp_le_exp.mpr ?_
    nlinarith [mul_le_mul_of_nonneg_right hr hd]
  -- D8.31.2: Cauchy–Schwarz over `B`
  have hnn : 0 ≤ (star u ⬝ᵥ u).re := (Complex.nonneg_iff.mp (dotProduct_star_self_nonneg _)).1
  have hux : (star u ⬝ᵥ u).re = (star x ⬝ᵥ (P *ᵥ x)).re := by
    have hPH : Pᴴ = P := hPproj.isSelfAdjoint.star_eq
    rw [star_mulVec, ← dotProduct_mulVec, hPH, hu]
  calc (star u ⬝ᵥ (A⁻¹ *ᵥ u)).re
      = (star (∑ B ∈ F, compProj D d k B *ᵥ u) ⬝ᵥ
          (A⁻¹ *ᵥ ∑ B ∈ F, compProj D d k B *ᵥ u)).re := by rw [hsum]
    _ ≤ F.card * ∑ B ∈ F, (star (compProj D d k B *ᵥ u) ⬝ᵥ
          (A⁻¹ *ᵥ (compProj D d k B *ᵥ u))).re :=
        re_dotProduct_sum_le_card_mul hA.inv.posSemidef F _
    _ ≤ F.card * ∑ B ∈ F, G * (star (compProj D d k B *ᵥ u) ⬝ᵥ (compProj D d k B *ᵥ u)).re :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hB) (by positivity)
    _ = F.card * (G * (star u ⬝ᵥ u).re) := by rw [← Finset.mul_sum, hnorm]
    _ ≤ Real.exp (k * Real.binEntropy τ) * (G * (star u ⬝ᵥ u).re) :=
        mul_le_mul_of_nonneg_right (card_filter_le hτ0 hτ k) (by positivity)
    _ = _ := by
        rw [hux, ← mul_assoc, ← Real.exp_add]
        congr 2
        ring

end Compression

/-! ## D8.31 The lower pin -/

section LowerPinSite

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} [∀ v, NeZero (n v)]
  {K : ℕ} {St : Type v} {X : Finset σ} (Γ : Statuses σ K St X)

omit [∀ v, NeZero (n v)] in
/-- `log(k + 2)/k → 0`. -/
theorem tendsto_log_add_two_div :
    Tendsto (fun k : ℕ => Real.log ((k : ℝ) + 2) / k) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 1 one_ne_zero).comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (2 : ℝ))))
  refine h.congr fun k => ?_
  simp only [Function.comp_apply, pow_one, one_mul]
  ring_nf

/-- For `k = 0` the band metric is the identity. -/
theorem bandA_zero (d : ℕ) [NeZero d] {t : ℝ} (ht : 0 ≤ t) (s : St) (g : Fin K) :
    Γ.bandA n d t 0 s g = 1 := by
  simp only [Statuses.bandA, Transport.bandMetric, Replicas.A,
    Replicas.W_zero (fun f => Fin (dims n d f)) ht, inv_one, one_pow, mul_one,
    add_sub_cancel]

/-- D8.31.4. A compressed-inverse bound `⟨Πx, A^{-1} Πx⟩ ≤ c ⟨x, Πx⟩` gives
`c^{-1} Π ≤ Π_k A + (1 - Π_k)`. -/
theorem lowProj_le_bandA (D : PhysData n) (d : ℕ) [NeZero d] {t : ℝ} (ht : 0 ≤ t) (τ : ℝ)
    (k : ℕ) (l : IrrepLabel (Equiv.Perm (Fin k))) (s : St) (g : Fin K) {c : ℝ} (hc : 0 < c)
    (h : ∀ x, (star (lowProj D d τ k l *ᵥ x) ⬝ᵥ ((Replicas.A (fun f => Fin (dims n d f)) t k
      (Γ.P s g) (Γ.Yr s g) (Γ.F s g))⁻¹ *ᵥ (lowProj D d τ k l *ᵥ x))).re ≤
        c * (star x ⬝ᵥ (lowProj D d τ k l *ᵥ x)).re) :
    c⁻¹ • lowProj D d τ k l ≤ Γ.bandA n d t k s g := by
  obtain ⟨hP, -, -, -, hS⟩ := lowProj_spec D d τ k l
  have hA : (Replicas.A (fun f => Fin (dims n d f)) t k (Γ.P s g) (Γ.Yr s g) (Γ.F s g)).PosDef :=
    (Replicas.eq_replicas_leaf_metric (fun f => Fin (dims n d f)) ht k (disjoint_P_Yr Γ s g)
      (disjoint_P_F Γ s g) (disjoint_Yr_F Γ s g)).2.2.2.2.1
  have h1 := le_of_compression_le hA hP hc h
  exact le_proj_mul_add_one_sub ⟨Transport.Pi_mul_Pi k, (Transport.isHermitian_Pi k).isSelfAdjoint⟩
    (Transport.commute_Pi_A t k _ _ _) hS hP.isSelfAdjoint h1

end LowerPinSite

/-! ## D8.31, rough -/

/-- D8.31 (rough half of `Step_8_31`, `a₀ = 1/5`, `C = 4`). -/
theorem step_8_31_rough {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} [∀ v, NeZero (n v)]
    (D : PhysData n) {X : Finset σ} (E : TypicalSet D X) {K : ℕ} {St : Type v}
    (Γ : Statuses σ K St X) (l : ∀ k : ℕ, IrrepLabel (Equiv.Perm (Fin k)))
    (hl : HighLabel E l) (a τ : ℝ) (ha : 0 < a) (ha₀ : a ≤ 1 / 5) (hτ0 : 0 < τ)
    (hτ : τ < 1 / 2) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧ ∀ (k : ℕ) (s : St) (g : Fin K),
      Real.exp (k * a * (2 * E.S' - 4 * (τ * Real.log E.d + Real.binEntropy τ / a)) -
          k * δ k) • lowProj D E.d τ k (l k) ≤ Γ.bandA n E.d (a / 2) k s g := by
  obtain ⟨c, N, -, ε, hε, hk⟩ := hl
  obtain ⟨C₁, -, hcomp⟩ := compression_rough D E.d Γ ha (by linarith)
  refine ⟨fun k => 2 * a * ε k + C₁ * (Real.log ((k : ℝ) + 2) / k), ?_, fun k s g => ?_⟩
  · simpa using (hε.const_mul (2 * a)).add (tendsto_log_add_two_div.const_mul C₁)
  obtain ⟨hP, -⟩ := lowProj_spec D E.d τ k (l k)
  have hPpsd : (lowProj D E.d τ k (l k)).PosSemidef := nonneg_iff_posSemidef.mp hP.nonneg
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp only [Nat.cast_zero, zero_mul, sub_self, Real.exp_zero, one_smul]
    rw [bandA_zero Γ E.d (by linarith)]
    exact sub_nonneg.mp hP.one_sub.nonneg
  -- D8.31.3: the exponent
  set E' := k * Real.binEntropy τ + C₁ * Real.log ((k : ℝ) + 2) - 2 * a * Real.log (l k).dim +
    2 * a * (τ * k) * Real.log E.d + 3 * a * (k * Real.binEntropy τ)
  have hpin := lowProj_le_bandA Γ D E.d (t := a / 2) (by linarith) τ k (l k) s g
    (Real.exp_pos E') (hcomp τ hτ0 hτ.le k (l k) s g)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk0
  have hd : 0 ≤ Real.log E.d := Real.log_nonneg (by exact_mod_cast NeZero.one_le)
  have hh : 0 ≤ Real.binEntropy τ := Real.binEntropy_nonneg hτ0.le (by linarith)
  have hlab : (k : ℝ) * E.S' - k * ε k ≤ Real.log (l k).dim := by
    have := (abs_le.mp (hk k).2).1
    linarith
  have hkδ : (k : ℝ) * (2 * a * ε k + C₁ * (Real.log ((k : ℝ) + 2) / k)) =
      2 * a * k * ε k + C₁ * Real.log ((k : ℝ) + 2) := by
    field_simp
  have hkL : (k : ℝ) * a * (2 * E.S' - 4 * (τ * Real.log E.d + Real.binEntropy τ / a)) =
      2 * k * a * E.S' - 4 * a * τ * k * Real.log E.d - 4 * k * Real.binEntropy τ := by
    field_simp
    ring
  have hexp : Real.exp (k * a * (2 * E.S' - 4 * (τ * Real.log E.d + Real.binEntropy τ / a)) -
      k * (2 * a * ε k + C₁ * (Real.log ((k : ℝ) + 2) / k))) ≤ (Real.exp E')⁻¹ := by
    rw [← Real.exp_neg, Real.exp_le_exp, hkL, hkδ]
    have h1 : 0 ≤ (3 - 3 * a) * (k * Real.binEntropy τ) :=
      mul_nonneg (by linarith) (mul_nonneg hkpos.le hh)
    have h2 : 0 ≤ a * (τ * k * Real.log E.d) :=
      mul_nonneg ha.le (mul_nonneg (mul_nonneg hτ0.le hkpos.le) hd)
    have h3 : 0 ≤ a * (Real.log (l k).dim - (k * E.S' - k * ε k)) :=
      mul_nonneg ha.le (by linarith)
    simp only [E']
    nlinarith
  calc _ ≤ (Real.exp E')⁻¹ • lowProj D E.d τ k (l k) := by
        rw [Matrix.le_iff, ← sub_smul]
        exact hPpsd.smul (sub_nonneg.mpr hexp)
    _ ≤ _ := hpin

/-- D8.30 (`comparator:component-inverse`). For `u_B ≠ 0`, `r = |B|`, sharp case
(`a ≤ a₀`, `a ≤ c/√𝓑` with `10a ≤ c₀/√𝓑`):
`⟨u_B, A_{j,g}^{-1} u_B⟩/‖u_B‖² ≤ poly(k) exp{-2kaS' - (k - r) a g^pre_{j,g} + 2ar log d_*
+ C a log binom(k, r) + C k a² 𝓑 + o(k)}`. Rough: omit the `g^pre` and `a²𝓑` terms.
`g^pre_{j,g} ≥ 0`. Stated before D8.27 is applied, with `θ = log d_{λ_k} - r log d_* -
log binom(k, r)` in place of `kS' - r log d_* - log binom(k, r) - o(k)`. -/
theorem step_8_30 :
    (type_of% @component_inverse_rough) ∧ (type_of% @component_inverse_sharp) ∧
      (type_of% @gpre_nonneg) :=
  ⟨@component_inverse_rough, @component_inverse_sharp, @gpre_nonneg⟩

/-! ## D8.31, sharp -/

section CompressionSharp

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} [∀ v, NeZero (n v)] (D : PhysData n)
  (d : ℕ) [NeZero d] {K : ℕ} {St : Type v} [Finite St] {X : Finset σ} (Γ : Statuses σ K St X)

/-- D8.31.2, D8.31.3 (sharp). `⟨Πx, A_{j,g}^{-1} Πx⟩ ≤ exp{k h(τ) + C log(k + 2) + C'
- 2a log d_{λ_k} + 2a τ k log d_* + 3a k h(τ) - (1 - τ) k a g^pre + 30 C₀ k a² 𝓑} ⟨x, Πx⟩`. -/
theorem compression_sharp {C₀ c₀ c : ℝ} (hC₀ : 0 < C₀)
    (hP : ∀ {Ω : Type u} [Fintype Ω] [DecidableEq Ω] (ρ : Matrix Ω Ω ℂ) (hρ : ρ.PosSemidef),
      ρ.trace = 1 → ∀ 𝓑 S : ℝ, 1 ≤ 𝓑 →
      (∀ u : ℝ, |u| ≤ c₀ / Real.sqrt 𝓑 → Real.log (trPowPos ρ hρ.isHermitian u) ≤
        u * S + C₀ * 𝓑 * u ^ 2) →
      ∃ Cp Np : ℝ, ∀ (k : ℕ) (u : ℝ), 0 ≤ u → u ≤ c / Real.sqrt 𝓑 → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
        Real.log (trace (TensorPower.tensorPow (k := k) ρ *
            cfc (fun x => Real.exp (ε * u * (x - k * S)))
              (labelObservable (TensorPower.copyPerm Ω k) fun l => Real.log l.dim))).re ≤
          2 * C₀ * k * 𝓑 * u ^ 2 + Cp + Np * Real.log (k + 1))
    {𝓑 : ℝ} (h𝓑 : MgfData D Γ C₀ c₀ 𝓑) {a : ℝ} (ha : 0 < a) (ha5 : 5 * a ≤ 1)
    (hac : 5 * a ≤ c / Real.sqrt 𝓑) :
    ∃ C₂ C₃ : ℝ, ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 → ∀ (k : ℕ)
      (l : IrrepLabel (Equiv.Perm (Fin k))) (s : St) (g : Fin K)
      (x : Transport.Config (dims n d) k → ℂ),
      (star (lowProj D d τ k l *ᵥ x) ⬝ᵥ ((Replicas.A (fun f => Fin (dims n d f)) (a / 2) k
          (Γ.P s g) (Γ.Yr s g) (Γ.F s g))⁻¹ *ᵥ (lowProj D d τ k l *ᵥ x))).re ≤
        Real.exp (k * Real.binEntropy τ + C₂ * Real.log ((k : ℝ) + 2) + C₃ -
          2 * a * Real.log l.dim + 2 * a * (τ * k) * Real.log d + 3 * a * (k * Real.binEntropy τ) -
            a * ((1 - τ) * k) * gpre D Γ s g + 30 * C₀ * k * 𝓑 * a ^ 2) *
          (star x ⬝ᵥ (lowProj D d τ k l *ᵥ x)).re := by
  have := Fintype.ofFinite St
  obtain ⟨C₂, C₃, hci⟩ := component_inverse_sharp D d Γ hC₀ hP h𝓑 ha ha5 hac
  refine ⟨C₂, C₃, fun τ hτ0 hτ k l s g x => ?_⟩
  obtain ⟨hPproj, -⟩ := lowProj_spec D d τ k l
  set P := lowProj D d τ k l
  set u := P *ᵥ x
  have hu : P *ᵥ u = u := by rw [mulVec_mulVec, hPproj.isIdempotentElem.eq]
  obtain ⟨hsum, hnorm, -⟩ := step_8_24 D d τ k l hu
  set F := Finset.univ.filter fun B : Finset (Fin k) => (B.card : ℝ) ≤ τ * k
  set A := Replicas.A (fun f => Fin (dims n d f)) (a / 2) k (Γ.P s g) (Γ.Yr s g) (Γ.F s g)
  have hA : A.PosDef := (Replicas.eq_replicas_leaf_metric (fun f => Fin (dims n d f))
    (by linarith : (0 : ℝ) ≤ a / 2) k (disjoint_P_Yr Γ s g) (disjoint_P_F Γ s g)
    (disjoint_Yr_F Γ s g)).2.2.2.2.1
  set G := Real.exp (C₂ * Real.log ((k : ℝ) + 2) + C₃ - 2 * a * Real.log l.dim +
    2 * a * (τ * k) * Real.log d + 3 * a * (k * Real.binEntropy τ) -
      a * ((1 - τ) * k) * gpre D Γ s g + 30 * C₀ * k * 𝓑 * a ^ 2)
  have hd : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast NeZero.one_le)
  have hgp : 0 ≤ gpre D Γ s g := gpre_nonneg Γ s g
  -- D8.31.3: the bound of D8.30 is uniform over `|B| ≤ τ k`
  have hB : ∀ B ∈ F, (star (compProj D d k B *ᵥ u) ⬝ᵥ (A⁻¹ *ᵥ (compProj D d k B *ᵥ u))).re ≤
      G * (star (compProj D d k B *ᵥ u) ⬝ᵥ (compProj D d k B *ᵥ u)).re := by
    intro B hBF
    have hr : (B.card : ℝ) ≤ τ * k := (Finset.mem_filter.mp hBF).2
    have hrk : B.card ≤ k := (Finset.card_le_univ B).trans (by simp)
    have hlc := log_choose_le hτ0 hτ hr hrk
    have hm : (Bᶜ.card : ℝ) = k - B.card := by
      rw [Finset.card_compl, Fintype.card_fin, Nat.cast_sub hrk]
    refine (hci τ k l u hu B s g).trans (mul_le_mul_of_nonneg_right ?_
      (Complex.nonneg_iff.mp (dotProduct_star_self_nonneg _)).1)
    refine Real.exp_le_exp.mpr ?_
    rw [hm]
    have h1 := mul_le_mul_of_nonneg_right hr hd
    have h2 : a * ((1 - τ) * k) * gpre D Γ s g ≤ a * (k - B.card) * gpre D Γ s g :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) ha.le) hgp
    nlinarith
  -- D8.31.2: Cauchy–Schwarz over `B`
  have hux : (star u ⬝ᵥ u).re = (star x ⬝ᵥ (P *ᵥ x)).re := by
    have hPH : Pᴴ = P := hPproj.isSelfAdjoint.star_eq
    rw [star_mulVec, ← dotProduct_mulVec, hPH, hu]
  have hnn : 0 ≤ (star u ⬝ᵥ u).re := (Complex.nonneg_iff.mp (dotProduct_star_self_nonneg _)).1
  calc (star u ⬝ᵥ (A⁻¹ *ᵥ u)).re
      = (star (∑ B ∈ F, compProj D d k B *ᵥ u) ⬝ᵥ
          (A⁻¹ *ᵥ ∑ B ∈ F, compProj D d k B *ᵥ u)).re := by rw [hsum]
    _ ≤ F.card * ∑ B ∈ F, (star (compProj D d k B *ᵥ u) ⬝ᵥ
          (A⁻¹ *ᵥ (compProj D d k B *ᵥ u))).re :=
        re_dotProduct_sum_le_card_mul hA.inv.posSemidef F _
    _ ≤ F.card * ∑ B ∈ F, G * (star (compProj D d k B *ᵥ u) ⬝ᵥ (compProj D d k B *ᵥ u)).re :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hB) (by positivity)
    _ = F.card * (G * (star u ⬝ᵥ u).re) := by rw [← Finset.mul_sum, hnorm]
    _ ≤ Real.exp (k * Real.binEntropy τ) * (G * (star u ⬝ᵥ u).re) :=
        mul_le_mul_of_nonneg_right (card_filter_le hτ0 hτ k) (by positivity)
    _ = _ := by
        rw [hux, ← mul_assoc, ← Real.exp_add]
        congr 2
        ring

end CompressionSharp

/-- D8.31 (sharp half of `Step_8_31`, `C' = 4 + 30 C₀`). -/
theorem step_8_31_sharp {C₀ c₀ c : ℝ} (hC₀ : 0 < C₀)
    (hP : ∀ {Ω : Type u} [Fintype Ω] [DecidableEq Ω] (ρ : Matrix Ω Ω ℂ) (hρ : ρ.PosSemidef),
      ρ.trace = 1 → ∀ 𝓑 S : ℝ, 1 ≤ 𝓑 →
      (∀ u : ℝ, |u| ≤ c₀ / Real.sqrt 𝓑 → Real.log (trPowPos ρ hρ.isHermitian u) ≤
        u * S + C₀ * 𝓑 * u ^ 2) →
      ∃ Cp Np : ℝ, ∀ (k : ℕ) (u : ℝ), 0 ≤ u → u ≤ c / Real.sqrt 𝓑 → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
        Real.log (trace (TensorPower.tensorPow (k := k) ρ *
            cfc (fun x => Real.exp (ε * u * (x - k * S)))
              (labelObservable (TensorPower.copyPerm Ω k) fun l => Real.log l.dim))).re ≤
          2 * C₀ * k * 𝓑 * u ^ 2 + Cp + Np * Real.log (k + 1))
    {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} [∀ v, NeZero (n v)]
    (D : PhysData n) {X : Finset σ} (E : TypicalSet D X) {K : ℕ} {St : Type v} [Finite St]
    (Γ : Statuses σ K St X) (l : ∀ k : ℕ, IrrepLabel (Equiv.Perm (Fin k)))
    (hl : HighLabel E l) {𝓑 : ℝ} (h𝓑 : MgfData D Γ C₀ c₀ 𝓑) (a τ : ℝ) (ha : 0 < a)
    (ha5 : 5 * a ≤ 1) (hac : 5 * a ≤ c / Real.sqrt 𝓑) (hτ0 : 0 < τ) (hτ : τ < 1 / 2) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧ ∀ (k : ℕ) (s : St) (g : Fin K),
      Real.exp (k * a * (2 * E.S' + (1 - τ) * gpre D Γ s g -
            (4 + 30 * C₀) * (τ * Real.log E.d + Real.binEntropy τ / a + a * 𝓑)) -
          k * δ k) • lowProj D E.d τ k (l k) ≤ Γ.bandA n E.d (a / 2) k s g := by
  obtain ⟨c', N, -, ε, hε, hk⟩ := hl
  obtain ⟨C₂, C₃, hcomp⟩ := compression_sharp D E.d Γ hC₀ hP h𝓑 ha ha5 hac
  refine ⟨fun k => 2 * a * ε k + (C₂ * Real.log ((k : ℝ) + 2) + C₃) / k, ?_, fun k s g => ?_⟩
  · have h1 : Tendsto (fun k : ℕ => C₃ / (k : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have h := ((hε.const_mul (2 * a)).add (tendsto_log_add_two_div.const_mul C₂)).add h1
    simp only [mul_zero, add_zero] at h
    refine h.congr fun k => ?_
    rw [add_div, mul_div_assoc]
    ring
  obtain ⟨hPj, -⟩ := lowProj_spec D E.d τ k (l k)
  have hPpsd : (lowProj D E.d τ k (l k)).PosSemidef := nonneg_iff_posSemidef.mp hPj.nonneg
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp only [Nat.cast_zero, zero_mul, sub_self, Real.exp_zero, one_smul]
    rw [bandA_zero Γ E.d (by linarith)]
    exact sub_nonneg.mp hPj.one_sub.nonneg
  set E' := k * Real.binEntropy τ + C₂ * Real.log ((k : ℝ) + 2) + C₃ -
    2 * a * Real.log (l k).dim + 2 * a * (τ * k) * Real.log E.d + 3 * a * (k * Real.binEntropy τ) -
      a * ((1 - τ) * k) * gpre D Γ s g + 30 * C₀ * k * 𝓑 * a ^ 2
  have hpin := lowProj_le_bandA Γ D E.d (t := a / 2) (by linarith) τ k (l k) s g
    (Real.exp_pos E') (hcomp τ hτ0 hτ.le k (l k) s g)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk0
  have hd : 0 ≤ Real.log E.d := Real.log_nonneg (by exact_mod_cast NeZero.one_le)
  have hh : 0 ≤ Real.binEntropy τ := Real.binEntropy_nonneg hτ0.le (by linarith)
  have h𝓑0 : 0 ≤ 𝓑 := by linarith [h𝓑.one_le]
  have ha1 : a ≤ 1 := by linarith
  have hlab : (k : ℝ) * E.S' - k * ε k ≤ Real.log (l k).dim := by
    have := (abs_le.mp (hk k).2).1
    linarith
  have hkδ : (k : ℝ) * (2 * a * ε k + (C₂ * Real.log ((k : ℝ) + 2) + C₃) / k) =
      2 * a * k * ε k + C₂ * Real.log ((k : ℝ) + 2) + C₃ := by
    field_simp
    ring
  have hkL : (k : ℝ) * a * (2 * E.S' + (1 - τ) * gpre D Γ s g -
      (4 + 30 * C₀) * (τ * Real.log E.d + Real.binEntropy τ / a + a * 𝓑)) =
      2 * k * a * E.S' + a * ((1 - τ) * k) * gpre D Γ s g -
        (4 + 30 * C₀) * (a * τ * k * Real.log E.d + k * Real.binEntropy τ + k * a ^ 2 * 𝓑) := by
    field_simp
  have hexp : Real.exp (k * a * (2 * E.S' + (1 - τ) * gpre D Γ s g -
      (4 + 30 * C₀) * (τ * Real.log E.d + Real.binEntropy τ / a + a * 𝓑)) -
      k * (2 * a * ε k + (C₂ * Real.log ((k : ℝ) + 2) + C₃) / k)) ≤ (Real.exp E')⁻¹ := by
    rw [← Real.exp_neg, Real.exp_le_exp, hkL, hkδ]
    have h1 : 0 ≤ (3 - 3 * a + 30 * C₀) * (k * Real.binEntropy τ) :=
      mul_nonneg (by linarith) (mul_nonneg hkpos.le hh)
    have h2 : 0 ≤ (2 + 30 * C₀) * (a * τ * k * Real.log E.d) :=
      mul_nonneg (by linarith) (mul_nonneg (mul_nonneg (mul_nonneg ha.le hτ0.le) hkpos.le) hd)
    have h3 : 0 ≤ a * (Real.log (l k).dim - (k * E.S' - k * ε k)) :=
      mul_nonneg ha.le (by linarith)
    have h4 : 0 ≤ 4 * (k * a ^ 2 * 𝓑) := by positivity
    simp only [E']
    nlinarith
  calc _ ≤ (Real.exp E')⁻¹ • lowProj D E.d τ k (l k) := by
        rw [Matrix.le_iff, ← sub_smul]
        exact hPpsd.smul (sub_nonneg.mpr hexp)
    _ ≤ _ := hpin

/-- D8.31 (`comparator:inverse-compression`, `comparator:lower-pin`). For `0 < τ < 1/2`:
`Π A_{j,g}^{-1} Π ≤ exp{-k a L_{j,g} + o(k)} Π`,
`L_{j,g} = 2S' + (1-τ) g^pre_{j,g} - C(τ log d_* + h(τ)/a + a𝓑)`. Rough: `g^pre = 0` and no
`a𝓑`. Equivalently `A_{j,g} ≥ exp{k a L_{j,g} - o(k)} Π`. -/
theorem step_8_31 (h10 : Step_8_10.{u}) : Step_8_31.{u, v} := by
  refine ⟨1 / 5, 4, by norm_num, by norm_num, ?_, ?_⟩
  · intro σ _ _ n _ D X E K St _ _ Γ l hl a τ ha ha₀ hτ0 hτ
    exact step_8_31_rough D E Γ l hl a τ ha ha₀ hτ0 hτ
  intro C₀ c₀ hC₀ hc₀
  obtain ⟨c₁, hc₁, hP⟩ := h10 C₀ c₀ hC₀ hc₀
  refine ⟨min (c₁ / 5) (1 / 5), 4 + 30 * C₀, lt_min (by positivity) (by norm_num),
    by positivity, ?_⟩
  intro σ _ _ n _ D X E K St _ _ Γ l hl 𝓑 h𝓑 a τ ha hac hτ0 hτ
  have hs : 1 ≤ Real.sqrt 𝓑 := Real.one_le_sqrt.mpr h𝓑.one_le
  have hs0 : 0 < Real.sqrt 𝓑 := by linarith
  have hm0 : 0 ≤ min (c₁ / 5) (1 / 5) := le_min (by positivity) (by norm_num)
  have ha' : a ≤ min (c₁ / 5) (1 / 5) := hac.trans (div_le_self hm0 hs)
  have ha5 : 5 * a ≤ 1 := by linarith [min_le_right (c₁ / 5) (1 / 5)]
  have hac5 : 5 * a ≤ c₁ / Real.sqrt 𝓑 := by
    have h1 := hac.trans (div_le_div_of_nonneg_right (min_le_left (c₁ / 5) (1 / 5)) hs0.le)
    have h2 : c₁ / 5 / Real.sqrt 𝓑 = c₁ / Real.sqrt 𝓑 / 5 := by ring
    rw [h2] at h1
    linarith
  exact step_8_31_sharp hC₀ hP D E Γ l hl h𝓑 a τ ha ha5 hac5 hτ0 hτ

end AreaLaw.Comparators
