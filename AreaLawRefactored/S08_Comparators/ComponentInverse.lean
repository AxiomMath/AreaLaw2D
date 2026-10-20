import AreaLawRefactored.S08_Comparators.Merge

/-!
# §8.4 The component inverse, sharp (D8.30)

Digest `digest/08-comparators.md` D8.30, paper `paper/sections/07-comparators.tex` 553–575.
The rough bound and the ingredients (D8.26–D8.29, the joint labels of a band, the physical
factors) are in `Merge.lean`. No geometry.
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix Filter Topology Arealaw Entropy PermutationRepresentation

namespace AreaLaw.Comparators

universe u v

set_option synthInstance.maxSize 256

/-- `∏_{j < 5} (T e^{E_j})^{1/5} = T e^{∑ E_j / 5}`. -/
theorem prod_rpow_fifth {T : ℝ} (hT : 0 ≤ T) (E : Fin 5 → ℝ) :
    ∏ j, (T * Real.exp (E j)) ^ ((5 : ℝ)⁻¹) = T * Real.exp ((∑ j, E j) / 5) := by
  simp only [Real.mul_rpow hT (Real.exp_pos _).le, ← Real.exp_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_sum]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hT, Finset.sum_div]
  norm_num
  exact Or.inl (Finset.sum_congr rfl fun j _ => by ring)

section Sharp

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} [∀ v, NeZero (n v)] (D : PhysData n)
  (d : ℕ) [NeZero d] {K : ℕ} {St : Type v} [Fintype St] {X : Finset σ} (Γ : Statuses σ K St X)

omit [Fintype σ] [DecidableEq σ] [∀ v, NeZero (n v)] [NeZero d] [Fintype St] in
/-- D8.30.4, pointwise: on the support,
`e^{-aG^good - aG^bad} ≤ e^{-2aθ} e^{aD_C} e^{aD_R} e^{-aF_Q} e^{-aF_V} e^{aF_Y}` (sharp). -/
private theorem sharp_pointwise {a θ lQ lV lY lC lR lP lF bP bF bY : ℝ} (ha : 0 < a)
    (hb : bY ≤ bP + bF) (hC : θ ≤ lC) (hR : θ ≤ lR) :
    Real.exp (-a * (lP + lF - lY + (bP + bF - bY))) ≤ Real.exp (-(2 * a * θ)) *
      (Real.exp (a * (lQ + lC - lP)) * (Real.exp (a * (lV + lR - lF)) *
        (Real.exp (-1 * a * lQ) * (Real.exp (-1 * a * lV) * Real.exp (1 * a * lY))))) := by
  simp only [← Real.exp_add]
  rw [Real.exp_le_exp]
  nlinarith

end Sharp

section SharpBound

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} [∀ v, NeZero (n v)] (D : PhysData n)
  (d : ℕ) [NeZero d] {K : ℕ} {St : Type v} [Finite St] {X : Finset σ} (Γ : Statuses σ K St X)

set_option maxHeartbeats 1000000 in
-- the final `nlinarith`/`linarith` steps over the five Hölder moments are heavy
/-- D8.30 (sharp). With D8.10 for the constant `c`, `𝓑 ≥ 1` and `5a ≤ min(1, c/√𝓑)`:
`⟨u_B, A_{j,g}^{-1} u_B⟩/‖u_B‖² ≤ poly(k) exp{-2aθ + a log binom(k, r) - (k - r) a g^pre_{j,g}
+ 30 C₀ k a² 𝓑}`, `θ = log d_{λ_k} - r log d_* - log binom(k, r)`. -/
theorem component_inverse_sharp {C₀ c₀ c : ℝ} (hC₀ : 0 < C₀)
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
    ∃ C₂ C₃ : ℝ, ∀ (τ : ℝ) (k : ℕ) (l : IrrepLabel (Equiv.Perm (Fin k)))
      (u : Transport.Config (dims n d) k → ℂ), lowProj D d τ k l *ᵥ u = u →
      ∀ (B : Finset (Fin k)) (s : St) (g : Fin K),
      (star (compProj D d k B *ᵥ u) ⬝ᵥ ((Replicas.A (fun f => Fin (dims n d f)) (a / 2) k
          (Γ.P s g) (Γ.Yr s g) (Γ.F s g))⁻¹ *ᵥ (compProj D d k B *ᵥ u))).re ≤
        Real.exp (C₂ * Real.log ((k : ℝ) + 2) + C₃ -
          2 * a * (Real.log l.dim - B.card * Real.log d - Real.log (k.choose B.card)) +
            a * Real.log (k.choose B.card) - a * Bᶜ.card * gpre D Γ s g +
              30 * C₀ * k * 𝓑 * a ^ 2) *
          (star (compProj D d k B *ᵥ u) ⬝ᵥ (compProj D d k B *ᵥ u)).re := by
  have := Fintype.ofFinite St
  obtain ⟨C, hC, hweights⟩ := component_inverse_weights D d Γ ha
  set Q₀ := Fintype.card (SiteConfig (dims n d))
  -- D8.10 for the three physical regions of every band
  have hreg : ∀ (s : St) (g : Fin K) (i : Fin 3), ∀ u : ℝ, |u| ≤ c₀ / Real.sqrt 𝓑 →
      Real.log (D.trPow (![X ∪ Γ.U s g, Γ.V s g, Γ.Y s g] i) u) ≤
        u * D.S (![X ∪ Γ.U s g, Γ.V s g, Γ.Y s g] i) + C₀ * 𝓑 * u ^ 2 := fun s g i =>
    h𝓑.bound s g _ (by fin_cases i <;> simp)
  have hex := fun s g i => phys_bound D d hP h𝓑.one_le _ (hreg s g i)
  choose Cp Np hCN using hex
  set Ctot := ∑ s, ∑ g, ∑ i, |Cp s g i|
  set Ntot := ∑ s, ∑ g, ∑ i, |Np s g i|
  have hCtot : ∀ s g i, |Cp s g i| ≤ Ctot := fun s g i =>
    (Finset.single_le_sum (f := fun i => |Cp s g i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ i)).trans
      ((Finset.single_le_sum (f := fun g => ∑ i, |Cp s g i|) (fun _ _ => Finset.sum_nonneg
        fun _ _ => abs_nonneg _) (Finset.mem_univ g)).trans
      (Finset.single_le_sum (f := fun s => ∑ g, ∑ i, |Cp s g i|) (fun _ _ => Finset.sum_nonneg
        fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ s)))
  have hNtot : ∀ s g i, |Np s g i| ≤ Ntot := fun s g i =>
    (Finset.single_le_sum (f := fun i => |Np s g i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ i)).trans
      ((Finset.single_le_sum (f := fun g => ∑ i, |Np s g i|) (fun _ _ => Finset.sum_nonneg
        fun _ _ => abs_nonneg _) (Finset.mem_univ g)).trans
      (Finset.single_le_sum (f := fun s => ∑ g, ∑ i, |Np s g i|) (fun _ _ => Finset.sum_nonneg
        fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ s)))
  refine ⟨C + 2 * (Q₀ ^ 2 : ℕ) / 5 + 3 * Ntot / 5, 3 * Ctot / 5,
    fun τ k l u hu B s g => ?_⟩
  set uB := compProj D d k B *ᵥ u
  set θ := Real.log l.dim - B.card * Real.log d - Real.log (k.choose B.card)
  set m := Bᶜ.card
  set W := IsOrthogonalResolution.weight (P := (Γ.band s g).jp (ι := fun f => Fin (dims n d f))
    (split B)) uB
  have hW0 : ∀ p, 0 ≤ W p := fun p => IsOrthogonalResolution.weight_nonneg
    ((Γ.band s g).resJ (split B)) ((Γ.band s g).isHermitian_jp (split B)) uB p
  set T := (star uB ⬝ᵥ uB).re
  have hT : 0 ≤ T := (Complex.nonneg_iff.mp (dotProduct_star_self_nonneg _)).1
  set XC : (Γ.band s g).Idx m B.card → ℝ := fun p => Real.exp (a * (Real.log
    p.1.1.1.1.1.1.dim + Real.log p.1.1.1.2.dim - Real.log p.1.2.1.dim))
  set XR : (Γ.band s g).Idx m B.card → ℝ := fun p => Real.exp (a * (Real.log
    p.1.1.1.1.1.2.dim + Real.log p.1.1.2.dim - Real.log p.1.2.2.dim))
  set YQ : (Γ.band s g).Idx m B.card → ℝ := fun p => Real.exp (-1 * a * Real.log p.1.1.1.1.1.1.dim)
  set YV : (Γ.band s g).Idx m B.card → ℝ := fun p => Real.exp (-1 * a * Real.log p.1.1.1.1.1.2.dim)
  set YY : (Γ.band s g).Idx m B.card → ℝ := fun p => Real.exp (1 * a * Real.log p.1.1.1.1.2.dim)
  set x : Fin 5 → (Γ.band s g).Idx m B.card → ℝ := ![XC, XR, YQ, YV, YY]
  have hx : ∀ p, ∏ j, x j p = XC p * XR p * YQ p * YV p * YY p := fun p => by
    simp [x, Fin.prod_univ_five]
  -- D8.30.1, D8.30.2 pointwise
  have hpt : ∀ p, Real.exp (-a * (Real.log p.1.2.1.dim + Real.log p.1.2.2.dim -
      Real.log p.1.1.1.1.2.dim + (Real.log p.2.1.1.dim + Real.log p.2.1.2.dim -
        Real.log p.2.2.dim))) * W p ≤ Real.exp (-(2 * a * θ)) * (W p * ∏ j, x j p) := by
    intro p
    by_cases hw : W p = 0
    · rw [hw]; simp
    obtain ⟨h1, -, h3, h4⟩ := support_compProj D d Γ τ l hu B s g p hw
    have := sharp_pointwise (lQ := Real.log p.1.1.1.1.1.1.dim) (lV := Real.log p.1.1.1.1.1.2.dim)
      (lY := Real.log p.1.1.1.1.2.dim) (lP := Real.log p.1.2.1.dim)
      (lF := Real.log p.1.2.2.dim) ha h1 h3 h4
    rw [hx]
    calc _ ≤ Real.exp (-(2 * a * θ)) * (XC p * (XR p * (YQ p * (YV p * YY p)))) * W p :=
          mul_le_mul_of_nonneg_right this (hW0 p)
      _ = _ := by ring
  have hx0 : ∀ j p, 0 ≤ x j p := fun j p => by fin_cases j <;> exact (Real.exp_pos _).le
  -- D8.30.4: Hölder with exponent 5
  have hH := sum_mul_prod_le_prod_rpow_sum (κ := Fin 5) (by simp) Finset.univ W x
    (fun p _ => hW0 p) (fun j p _ => hx0 j p)
  simp only [Fintype.card_fin, Nat.cast_ofNat] at hH
  -- the five moments
  have hmm := merge_moments_compProj D d Γ τ l hu B s g (b := 5 * a) ha5
  have hpow : ∀ (z : ℝ), Real.exp z ^ 5 = Real.exp (5 * z) := fun z => by
    rw [← Real.exp_nat_mul]; norm_num
  have hq := fun f => re_dotProduct_hom_ofReal ((Γ.band s g).resJ (ι := fun f => Fin (dims n d f))
    (split B)) f uB
  set E : Fin 5 → ℝ := ![(Q₀ ^ 2 : ℕ) * Real.log ((k : ℝ) + 2),
    (Q₀ ^ 2 : ℕ) * Real.log ((k : ℝ) + 2),
    -1 * (5 * a) * m * D.S (X ∪ Γ.U s g) + 2 * C₀ * m * 𝓑 * (5 * a) ^ 2 + Cp s g 0 +
      Np s g 0 * Real.log (m + 1),
    -1 * (5 * a) * m * D.S (Γ.V s g) + 2 * C₀ * m * 𝓑 * (5 * a) ^ 2 + Cp s g 1 +
      Np s g 1 * Real.log (m + 1),
    1 * (5 * a) * m * D.S (Γ.Y s g) + 2 * C₀ * m * 𝓑 * (5 * a) ^ 2 + Cp s g 2 +
      Np s g 2 * Real.log (m + 1)]
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hpolyE : ((k : ℝ) + 2) ^ Q₀ ^ 2 = Real.exp ((Q₀ ^ 2 : ℕ) * Real.log ((k : ℝ) + 2)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hk2, mul_comm]
  have hC5 : ∑ p, W p * XC p ^ 5 ≤ T * Real.exp ((Q₀ ^ 2 : ℕ) * Real.log ((k : ℝ) + 2)) := by
    have h := (Γ.band s g).hom_mergeC (ι := fun f => Fin (dims n d f)) (split B) (5 * a)
    have h' := hq (fun p => Real.exp (5 * a * (Real.log p.1.1.1.1.1.1.dim +
      Real.log p.1.1.1.2.dim - Real.log p.1.2.1.dim)))
    rw [h] at h'
    calc _ = _ := Finset.sum_congr rfl fun p _ => by
            simp only [XC]; rw [hpow, mul_comm]; ring_nf; rfl
      _ ≤ _ := h' ▸ hmm.1
      _ = _ := by rw [hpolyE, mul_comm]
  have hR5 : ∑ p, W p * XR p ^ 5 ≤ T * Real.exp ((Q₀ ^ 2 : ℕ) * Real.log ((k : ℝ) + 2)) := by
    have h := (Γ.band s g).hom_mergeR (ι := fun f => Fin (dims n d f)) (split B) (5 * a)
    have h' := hq (fun p => Real.exp (5 * a * (Real.log p.1.1.1.1.1.2.dim +
      Real.log p.1.1.2.dim - Real.log p.1.2.2.dim)))
    rw [h] at h'
    calc _ = _ := Finset.sum_congr rfl fun p _ => by
            simp only [XR]; rw [hpow, mul_comm]; ring_nf; rfl
      _ ≤ _ := h' ▸ hmm.2
      _ = _ := by rw [hpolyE, mul_comm]
  have h5a : 0 ≤ 5 * a := by positivity
  have hQ5 : ∑ p, W p * YQ p ^ 5 ≤ T * Real.exp (E 2) := by
    have h := (Γ.band s g).hom_Q (ι := fun f => Fin (dims n d f)) (split B)
      (fun l => Real.exp (-1 * (5 * a) * Real.log l.dim))
    have h' := hq (fun p => Real.exp (-1 * (5 * a) * Real.log p.1.1.1.1.1.1.dim))
    rw [h] at h'
    calc _ = _ := Finset.sum_congr rfl fun p _ => by
            simp only [YQ]; rw [hpow, mul_comm]; ring_nf; rfl
      _ ≤ _ := h' ▸ hCN s g 0 k B u (5 * a) h5a hac (-1) (Or.inr rfl)
  have hV5 : ∑ p, W p * YV p ^ 5 ≤ T * Real.exp (E 3) := by
    have h := (Γ.band s g).hom_V (ι := fun f => Fin (dims n d f)) (split B)
      (fun l => Real.exp (-1 * (5 * a) * Real.log l.dim))
    have h' := hq (fun p => Real.exp (-1 * (5 * a) * Real.log p.1.1.1.1.1.2.dim))
    rw [h] at h'
    calc _ = _ := Finset.sum_congr rfl fun p _ => by
            simp only [YV]; rw [hpow, mul_comm]; ring_nf; rfl
      _ ≤ _ := h' ▸ hCN s g 1 k B u (5 * a) h5a hac (-1) (Or.inr rfl)
  have hY5 : ∑ p, W p * YY p ^ 5 ≤ T * Real.exp (E 4) := by
    have h := (Γ.band s g).hom_Y (ι := fun f => Fin (dims n d f)) (split B)
      (fun l => Real.exp (1 * (5 * a) * Real.log l.dim))
    have h' := hq (fun p => Real.exp (1 * (5 * a) * Real.log p.1.1.1.1.2.dim))
    rw [h] at h'
    calc _ = _ := Finset.sum_congr rfl fun p _ => by
            simp only [YY]; rw [hpow, mul_comm]; ring_nf; rfl
      _ ≤ _ := h' ▸ hCN s g 2 k B u (5 * a) h5a hac 1 (Or.inl rfl)
  have hmom : ∀ j, ∑ p, W p * x j p ^ 5 ≤ T * Real.exp (E j) := by
    intro j
    fin_cases j
    · exact hC5
    · exact hR5
    · exact hQ5
    · exact hV5
    · exact hY5
  have hprod : ∏ j, (∑ p, W p * x j p ^ 5) ^ ((5 : ℝ)⁻¹) ≤ T * Real.exp ((∑ j, E j) / 5) := by
    rw [← prod_rpow_fifth hT E]
    exact Finset.prod_le_prod (fun j _ => Real.rpow_nonneg (Finset.sum_nonneg fun p _ =>
      mul_nonneg (hW0 p) (pow_nonneg (hx0 j p) _)) _)
      fun j _ => Real.rpow_le_rpow (Finset.sum_nonneg fun p _ => mul_nonneg (hW0 p)
        (pow_nonneg (hx0 j p) _)) (hmom j) (by norm_num)
  -- D8.30.5: combine
  have hsum : ∑ p, Real.exp (-a * (Real.log p.1.2.1.dim + Real.log p.1.2.2.dim -
      Real.log p.1.1.1.1.2.dim + (Real.log p.2.1.1.dim + Real.log p.2.1.2.dim -
        Real.log p.2.2.dim))) * W p ≤
      Real.exp (-(2 * a * θ)) * (T * Real.exp ((∑ j, E j) / 5)) := by
    calc _ ≤ ∑ p, Real.exp (-(2 * a * θ)) * (W p * ∏ j, x j p) := Finset.sum_le_sum fun p _ =>
          hpt p
      _ = Real.exp (-(2 * a * θ)) * ∑ p, W p * ∏ j, x j p := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hH.trans hprod) (Real.exp_pos _).le
  have hch : (0 : ℝ) < k.choose B.card := by
    exact_mod_cast Nat.choose_pos ((Finset.card_le_univ B).trans (by simp))
  have hm : (m : ℝ) ≤ k := by exact_mod_cast (Finset.card_le_univ _).trans (by simp)
  have hL1 : 0 ≤ Real.log ((m : ℝ) + 1) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have hL2 : Real.log ((m : ℝ) + 1) ≤ Real.log ((k : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hNp : ∀ i, Np s g i * Real.log ((m : ℝ) + 1) ≤ Ntot * Real.log ((k : ℝ) + 2) := fun i =>
    calc Np s g i * Real.log ((m : ℝ) + 1) ≤ |Np s g i| * Real.log ((m : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hL1
      _ ≤ Ntot * Real.log ((m : ℝ) + 1) := mul_le_mul_of_nonneg_right (hNtot s g i) hL1
      _ ≤ Ntot * Real.log ((k : ℝ) + 2) :=
          mul_le_mul_of_nonneg_left hL2 ((abs_nonneg _).trans (hNtot s g 0))
  have hCp : ∀ i, Cp s g i ≤ Ctot := fun i => (le_abs_self _).trans (hCtot s g i)
  have hmB : (m : ℝ) * 𝓑 * a ^ 2 ≤ k * 𝓑 * a ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm (by linarith [h𝓑.one_le]))
      (by positivity)
  have hsE : ∑ j, E j = 2 * ((Q₀ ^ 2 : ℕ) * Real.log ((k : ℝ) + 2)) -
      5 * a * m * gpre D Γ s g + 150 * C₀ * m * 𝓑 * a ^ 2 +
      (Cp s g 0 + Cp s g 1 + Cp s g 2) + (Np s g 0 + Np s g 1 + Np s g 2) *
        Real.log ((m : ℝ) + 1) := by
    simp only [E, Fin.sum_univ_five, gpre]
    simp
    ring
  calc _ ≤ ((k : ℝ) + 2) ^ C * (k.choose B.card : ℝ) ^ a * (Real.exp (-(2 * a * θ)) *
        (T * Real.exp ((∑ j, E j) / 5))) := (hweights k u B s g).trans
          (mul_le_mul_of_nonneg_left hsum (by positivity))
    _ = Real.exp (C * Real.log ((k : ℝ) + 2) + a * Real.log (k.choose B.card) - 2 * a * θ +
          (∑ j, E j) / 5) * T := by
        rw [Real.rpow_def_of_pos hk2, Real.rpow_def_of_pos hch]
        rw [show Real.exp (Real.log ((k : ℝ) + 2) * C) * Real.exp (Real.log (k.choose B.card) * a) *
            (Real.exp (-(2 * a * θ)) * (T * Real.exp ((∑ j, E j) / 5))) =
            Real.exp (Real.log ((k : ℝ) + 2) * C + Real.log (k.choose B.card) * a +
              -(2 * a * θ) + (∑ j, E j) / 5) * T by
          rw [Real.exp_add, Real.exp_add, Real.exp_add]; ring]
        congr 2
        ring
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) hT
        rw [hsE]
        have := hNp 0
        have := hNp 1
        have := hNp 2
        have := hCp 0
        have := hCp 1
        have := hCp 2
        have := mul_le_mul_of_nonneg_left hmB hC₀.le
        linarith

end SharpBound

end AreaLaw.Comparators
