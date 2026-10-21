import AreaLaw.S09_Scanner.Interfaces
import AreaLawForMathlib.QuantumInfo.RegionRelabel

/-!
# §9.0 The truncated system (D9.3) and the transfer `Ω → Ω̃` (D9.9.1)

Digest `digest/09-scanner.md` (D9.3, D9.9.1), paper `paper/sections/08-scanner.tex` lines 43–64,
399–410. Graph-level (Map.md, Dimension: `any d`): a simple graph `G` on a site type `σ` with
ball growth `V r ≤ K₀ (r+1)^{m₀}`, the depth `dep` and the test geometry `TestGeometry`.

The truncated system of Proposition 4.5 at `S₀ = A ∩ T_L` is a `Comparators.PhysData` on the
site type `↥Λ`; its Hamiltonian is presented as §7 energy terms. Two facts about any
`PhysData` with energy terms are proved first: Lemma 3.1 for its marginals (with the budget
`𝓑` of the terms crossing the cut) and `H̄ = ∑ h̄_i` on `𝒱 = 𝓗_phys ⊗ 𝓗_C ⊗ 𝓗_R`.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Arealaw Finset Entropy
open OpenAI (pureState HasGlobalGap)

namespace AreaLaw.Scanner

open Comparators Transport GraphDomain

universe u

/-! ## Energy terms of a physical system -/

section EnergyTerms

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

theorem localLift_submatrix_univEquiv (D : Finset V)
    (K : Matrix (RegionConfig n D) (RegionConfig n D) ℂ) :
    (localLift D K).submatrix univEquiv univEquiv =
      extendId (loc := fun v => Fin (n v)) (subset_univ D) K := by
  ext w w'
  simp only [submatrix_apply, localLift_apply, extendId, of_apply]
  have : (∀ v ∉ D, univEquiv w v = univEquiv w' v) ↔
      restr (S := univ \ D) sdiff_subset w = restr (S := univ \ D) sdiff_subset w' := by
    constructor
    · intro h
      funext j
      exact h j.1 (mem_sdiff.1 j.2).2
    · intro h v hv
      exact congrFun h ⟨v, mem_sdiff.2 ⟨mem_univ v, hv⟩⟩
  simp only [this]
  rfl

variable {ι : Type}

/-- The budget `𝓑 = 1 + ∑_{i crossing} log² (e d_i)` of Lemma 3.1 for the cut `Q`: the sum runs
over the terms whose designated support meets both `Q` and its complement. -/
noncomputable def budget [Fintype ι] (Et : EnergyTerms V n ι) (Q : Finset V) : ℝ :=
  1 + ∑ i ∈ univ.filter (fun i => (Et.support i ∩ Q).Nonempty ∧ (Et.support i \ Q).Nonempty),
    Real.log (Real.exp 1 * Fintype.card (RegionConfig n (Et.support i))) ^ 2

/-- The budget of a cut is the budget of its complement. -/
theorem budget_compl [Fintype ι] (Et : EnergyTerms V n ι) (Q : Finset V) :
    budget Et (univ \ Q) = budget Et Q := by
  unfold budget
  congr 1
  refine sum_congr (filter_congr fun i _ => ?_) fun _ _ => rfl
  rw [← compl_eq_univ_sdiff, ← sdiff_eq_inter_compl, sdiff_compl, inf_eq_inter, and_comm]

theorem extendId_op_nonneg (Et : EnergyTerms V n ι) (i : ι) :
    0 ≤ extendId (loc := fun v => Fin (n v)) (subset_univ (Et.support i)) (Et.op i) := by
  rw [Matrix.nonneg_iff_posSemidef]
  exact posSemidef_extendId _ ((Matrix.nonneg_iff_posSemidef).1 (Et.nonneg i))

theorem extendId_op_le_one (Et : EnergyTerms V n ι) (i : ι) :
    extendId (loc := fun v => Fin (n v)) (subset_univ (Et.support i)) (Et.op i) ≤ 1 := by
  rw [Matrix.le_iff]
  have : (1 : Matrix (Reg (fun v => Fin (n v)) univ) (Reg (fun v => Fin (n v)) univ) ℂ) -
      extendId (subset_univ (Et.support i)) (Et.op i) =
      extendId (subset_univ (Et.support i)) (1 - Et.op i) := by
    rw [sub_eq_add_neg, sub_eq_add_neg, extendId_add, extendId_one, ← neg_one_smul ℂ (Et.op i),
      extendId_smul, neg_one_smul]
  rw [this]
  exact posSemidef_extendId _ (Matrix.le_iff.1 (Et.le_one i))

theorem trPow_eq (D : PhysData n) (Q : Finset V) (u : ℝ) :
    D.trPow Q u = ∑ j ∈ univ.filter (fun j => 0 < D.p Q j),
      D.p Q j * Real.exp (-u * Real.log (D.p Q j)) := by
  change (∑ j, if 0 < D.p Q j then D.p Q j ^ (1 - u) else 0) = _
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hj
  · rw [Real.rpow_def_of_pos hj, show Real.log (D.p Q j) * (1 - u) = Real.log (D.p Q j) +
      -u * Real.log (D.p Q j) by ring, Real.exp_add, Real.exp_log hj]
  · rfl

/-- D3.1 (Lemma 3.1) for a physical system `Ω̃` whose Hamiltonian is a sum of energy terms
`0 ≤ h_i ≤ 1` (`c₀ = 1`, `g₀ = g̃`, `ϑ = 1/g̃`), at the cut `Q`. -/
theorem lemma_3_1_physData [Fintype ι] (D : PhysData n) (Et : EnergyTerms V n ι)
    (hH : D.H = ∑ i, Et.term i) (Q : Finset V) :
    (∀ u : ℝ, |u| ≤ (32 * Real.sqrt ((1 + 1 / D.g) * budget Et Q))⁻¹ →
      Real.log (D.trPow Q u) ≤ u * D.S Q + 512 * Real.exp 1 * (1 / D.g) * budget Et Q * u ^ 2) ∧
    ∀ w : ℝ, 0 ≤ w →
      ∑ j ∈ univ.filter (fun j => 0 < D.p Q j ∧ w < |-Real.log (D.p Q j) - D.S Q|), D.p Q j ≤
        min 1 (2 * Real.exp (Real.exp 1 / 2) *
          Real.exp (-(w / (32 * Real.sqrt ((1 + 1 / D.g) * budget Et Q))))) := by
  have hterm (i : ι) : (Et.term i).submatrix univEquiv univEquiv =
      extendId (loc := fun v => Fin (n v)) (subset_univ (Et.support i)) (Et.op i) :=
    localLift_submatrix_univEquiv _ _
  have hsum : ∑ i, (Et.term i).submatrix univEquiv univEquiv =
      D.H.submatrix univEquiv univEquiv := by
    rw [hH]; ext x y; simp [Matrix.sum_apply]
  obtain ⟨h1, h2⟩ := lemma_3_1 (σ := V) (loc := fun v => Fin (n v)) univ ι
    (fun i => Et.support i) (fun i => subset_univ _)
    (fun i => (Et.term i).submatrix univEquiv univEquiv) 1 D.g D.E₀
    (D.Ω ∘ univEquiv) D.norm_Ω_univEquiv (fun i => ⟨Et.op i, hterm i⟩)
    (fun i => by
      rw [hterm]
      exact ((Matrix.nonneg_iff_posSemidef).1 (extendId_op_nonneg Et i)).isHermitian)
    zero_le_one
    (fun i => by
      rw [hterm]
      exact l2_opNorm_le_one_of_nonneg_of_le_one (extendId_op_nonneg Et i)
        (extendId_op_le_one Et i))
    D.gap_pos
    (by rw [hsum, submatrix_mulVec_equiv, Function.comp_assoc, Equiv.self_comp_symm,
      Function.comp_id, D.ground]; rfl)
    (by rw [hsum]; exact hasGlobalGap_submatrix univEquiv D.gap)
    Q (subset_univ Q)
  refine ⟨fun u hu => ?_, fun w hw => h2 w hw⟩
  rw [trPow_eq]
  exact h1 u hu

omit [Fintype V] [DecidableEq V] in
theorem phys_mem_physReg {D : Finset V} {v : V} : Site.phys v ∈ physReg D ↔ v ∈ D :=
  Finset.mem_map' _

/-- The physical part of a regional configuration of `𝒱` on `physReg D`. -/
noncomputable def physRegEquiv (d : ℕ) (D : Finset V) :
    RegionConfig (dims n d) (physReg D) ≃ RegionConfig n D where
  toFun x v := x ⟨.phys v.1, phys_mem_physReg.2 v.2⟩
  invFun y s := Site.rec (motive := fun s => s ∈ physReg D → Fin (dims n d s))
    (fun v hv => y ⟨v, phys_mem_physReg.1 hv⟩)
    (fun h => absurd h (by simp [physReg]))
    (fun h => absurd h (by simp [physReg])) s.1 s.2
  left_inv x := by
    funext ⟨s, hs⟩
    cases s with
    | phys v => rfl
    | C => exact absurd hs (by simp [physReg])
    | R => exact absurd hs (by simp [physReg])
  right_inv _ := rfl

/-- The energy terms `h_i ⊗ 1_{CR}` on `𝒱`, with designated supports `physReg D_i`. -/
noncomputable def siteTerms (Et : EnergyTerms V n ι) (d : ℕ) :
    EnergyTerms (Site V) (dims n d) ι where
  support i := physReg (Et.support i)
  op i := (Et.op i).submatrix (physRegEquiv d _) (physRegEquiv d _)
  nonneg i := by
    rw [Matrix.nonneg_iff_posSemidef]
    exact ((Matrix.nonneg_iff_posSemidef).1 (Et.nonneg i)).submatrix _
  le_one i := by
    rw [Matrix.le_iff, ← submatrix_one_equiv (physRegEquiv (n := n) d (Et.support i))]
    exact (Matrix.le_iff.1 (Et.le_one i)).submatrix _

theorem term_siteTerms (Et : EnergyTerms V n ι) (d : ℕ) (i : ι) (x y : SiteConfig (dims n d)) :
    (siteTerms Et d).term i x y =
      Et.term i (physPart x) (physPart y) * if x .C = y .C ∧ x .R = y .R then 1 else 0 := by
  simp only [EnergyTerms.term, localLift_apply, siteTerms]
  have hc : (∀ s ∉ physReg (Et.support i), x s = y s) ↔
      (∀ v ∉ Et.support i, physPart x v = physPart y v) ∧ (x .C = y .C ∧ x .R = y .R) := by
    constructor
    · intro h
      exact ⟨fun v hv => h _ (fun h' => hv (phys_mem_physReg.1 h')),
        h _ (by simp [physReg]), h _ (by simp [physReg])⟩
    · rintro ⟨h, hC, hR⟩ s hs
      cases s with
      | phys v => exact h v (fun h' => hs (phys_mem_physReg.2 h'))
      | C => exact hC
      | R => exact hR
  by_cases h1 : ∀ v ∉ Et.support i, physPart x v = physPart y v
  · by_cases h2 : x .C = y .C ∧ x .R = y .R
    · rw [if_pos (hc.2 ⟨h1, h2⟩), if_pos h1, if_pos h2, mul_one]; rfl
    · rw [if_neg (fun h => h2 (hc.1 h).2), if_neg h2, mul_zero]
  · rw [if_neg (fun h => h1 (hc.1 h).1), if_neg h1, zero_mul]

/-- `H̃ ⊗ 1_{CR} = ∑_i h_i ⊗ 1_{CR}` on one copy of `𝒱`. -/
theorem Hx_eq [Fintype ι] (D : PhysData n) (Et : EnergyTerms V n ι)
    (hH : D.H = ∑ i, Et.term i) (d : ℕ) : Hx D d = ∑ i, (siteTerms Et d).term i := by
  ext x y
  simp only [Hx, hH, Matrix.sum_apply, Finset.sum_mul, term_siteTerms]

/-- D8.8, D7.12. The copy mean of `H̃` is §7's `H̄ = ∑_i h̄_i` of the energy terms on `𝒱`, by
linearity of the copy mean. -/
theorem Hbar_eq [Fintype ι] (D : PhysData n) (Et : EnergyTerms V n ι)
    (hH : D.H = ∑ i, Et.term i) (d k : ℕ) : Hbar D d k = (siteTerms Et d).Hbar k := by
  simp only [Hbar, EnergyTerms.Hbar, EnergyTerms.hbar, TensorPower.copyMean, Hx_eq D Et hH d,
    TensorPower.siteOp_sum, Finset.smul_sum]
  exact Finset.sum_comm

end EnergyTerms

/-! ## Local operators on a finite domain -/

section Domain

variable {σ : Type u} [DecidableEq σ] {Λ : Finset σ} {q : ℕ}

omit [DecidableEq σ] in
theorem mem_up {Q : Finset Λ} {x : σ} : x ∈ up Q ↔ ∃ h : x ∈ Λ, (⟨x, h⟩ : Λ) ∈ Q := by
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := mem_map.1 hx
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact mem_map_of_mem _ hx

theorem subtype_inter_nonempty_iff (S : Finset σ) (Q : Finset Λ) :
    (S.subtype (· ∈ Λ) ∩ Q).Nonempty ↔ (S ∩ up Q).Nonempty := by
  constructor
  · rintro ⟨x, hx⟩
    rw [mem_inter, mem_subtype] at hx
    exact ⟨x.1, mem_inter.2 ⟨hx.1, mem_up.2 ⟨x.2, hx.2⟩⟩⟩
  · rintro ⟨x, hx⟩
    rw [mem_inter, mem_up] at hx
    obtain ⟨hxS, hΛ, hQ⟩ := hx
    exact ⟨⟨x, hΛ⟩, mem_inter.2 ⟨mem_subtype.2 hxS, hQ⟩⟩

theorem subtype_sdiff_nonempty_iff (S : Finset σ) (Q : Finset Λ) :
    (S.subtype (· ∈ Λ) \ Q).Nonempty ↔ (S ∩ (Λ \ up Q)).Nonempty := by
  constructor
  · rintro ⟨x, hx⟩
    rw [mem_sdiff, mem_subtype] at hx
    refine ⟨x.1, mem_inter.2 ⟨hx.1, mem_sdiff.2 ⟨x.2, fun h => hx.2 ?_⟩⟩⟩
    obtain ⟨_, h'⟩ := mem_up.1 h
    exact h'
  · rintro ⟨x, hx⟩
    rw [mem_inter, mem_sdiff] at hx
    obtain ⟨hxS, hΛ, hQ⟩ := hx
    exact ⟨⟨x, hΛ⟩, mem_sdiff.2 ⟨mem_subtype.2 hxS, fun h => hQ (mem_up.2 ⟨hΛ, h⟩)⟩⟩

theorem card_regionConfig_subtype {S : Finset σ} (hS : S ⊆ Λ) :
    Fintype.card (RegionConfig (fun _ : Λ => q) (S.subtype (· ∈ Λ))) = q ^ #S := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin, prod_const, card_univ, Fintype.card_coe, card_subtype,
    filter_true_of_mem fun x hx => hS hx]

theorem restr_eq_iff {S : Finset σ} (x y : Reg (fun _ : σ => Fin q) Λ) :
    restr (S := Λ \ S) sdiff_subset x = restr (S := Λ \ S) sdiff_subset y ↔
      ∀ v : Λ, v ∉ S.subtype (· ∈ Λ) → x v = y v := by
  constructor
  · intro h v hv
    have hv' : v.1 ∈ Λ \ S := mem_sdiff.2 ⟨v.2, fun h' => hv (mem_subtype.2 h')⟩
    exact congrFun h ⟨v.1, hv'⟩
  · intro h
    funext j
    obtain ⟨j, hj⟩ := j
    rw [mem_sdiff] at hj
    have hj' : (⟨j, hj.1⟩ : Λ) ∉ S.subtype (· ∈ Λ) := by
      rw [mem_subtype]
      exact hj.2
    exact h _ hj'

/-- Configurations of `S ⊆ Λ` read on the site type `↥Λ`. -/
def subtypeEquiv {S : Finset σ} (hS : S ⊆ Λ) :
    RegionConfig (fun _ : Λ => q) (S.subtype (· ∈ Λ)) ≃ Reg (fun _ : σ => Fin q) S where
  toFun x j := x ⟨⟨j.1, hS j.2⟩, mem_subtype.2 j.2⟩
  invFun y i := y ⟨i.1.1, mem_subtype.1 i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The lift to `↥Λ` of a local operator on `S ⊆ Λ` is its extension by the identity. -/
theorem localLift_subtype {S : Finset σ} (hS : S ⊆ Λ)
    (K : Matrix (Reg (fun _ : σ => Fin q) S) (Reg (fun _ : σ => Fin q) S) ℂ) :
    localLift (n := fun _ : Λ => q) (S.subtype (· ∈ Λ))
        (K.submatrix (subtypeEquiv hS) (subtypeEquiv hS)) = extendId hS K := by
  ext x y
  simp only [localLift_apply, extendId, of_apply]
  by_cases h : ∀ v ∉ S.subtype (· ∈ Λ), x v = y v
  · rw [if_pos h, if_pos ((restr_eq_iff x y).2 h)]; rfl
  · rw [if_neg h, if_neg (fun h' => h ((restr_eq_iff x y).1 h'))]

theorem extendId_one_sub {S : Finset σ} (hS : S ⊆ Λ)
    (B : Matrix (Reg (fun _ : σ => Fin q) S) (Reg (fun _ : σ => Fin q) S) ℂ) :
    extendId hS (1 - B) = 1 - extendId hS B := by
  rw [sub_eq_add_neg, sub_eq_add_neg, extendId_add, extendId_one, ← neg_one_smul ℂ B,
    extendId_smul, neg_one_smul]

theorem ptrace_extendId {S : Finset σ} (hS : S ⊆ Λ)
    (M : Matrix (Reg (fun _ : σ => Fin q) S) (Reg (fun _ : σ => Fin q) S) ℂ) :
    ptrace hS (extendId hS M) = (Fintype.card (Reg (fun _ : σ => Fin q) (Λ \ S)) : ℂ) • M := by
  ext x y
  simp [ptrace, extendId_apply_glue]

/-- An operator `0 ≤ h ≤ 1` supported in `S` is the extension of a local `0 ≤ B ≤ 1`. -/
theorem exists_op [NeZero q] {S : Finset σ} (hS : S ⊆ Λ)
    {h : Matrix (Reg (fun _ : σ => Fin q) Λ) (Reg (fun _ : σ => Fin q) Λ) ℂ}
    (hh : OpenAI.IsSupportedOn hS h) (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    ∃ B : Matrix (Reg (fun _ : σ => Fin q) S) (Reg (fun _ : σ => Fin q) S) ℂ,
      h = extendId hS B ∧ 0 ≤ B ∧ B ≤ 1 := by
  obtain ⟨B, rfl⟩ := hh
  set c : ℝ := (Fintype.card (Reg (fun _ : σ => Fin q) (Λ \ S)) : ℝ)
  have hc : 0 < c := by
    have : Nonempty (Reg (fun _ : σ => Fin q) (Λ \ S)) :=
      ⟨fun _ => ⟨0, Nat.pos_of_ne_zero (NeZero.ne q)⟩⟩
    exact Nat.cast_pos.2 Fintype.card_pos
  have hpt : ∀ M : Matrix (Reg (fun _ : σ => Fin q) S) (Reg (fun _ : σ => Fin q) S) ℂ,
      M = c⁻¹ • ptrace hS (extendId hS M) := fun M => by
    rw [ptrace_extendId]
    ext i j
    simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul, c]
    push_cast
    field_simp
  refine ⟨B, rfl, ?_, ?_⟩
  · rw [hpt B, Matrix.nonneg_iff_posSemidef]
    exact (posSemidef_ptrace hS ((Matrix.nonneg_iff_posSemidef).1 h0)).smul (inv_nonneg.2 hc.le)
  · rw [Matrix.le_iff, hpt (1 - B), extendId_one_sub]
    exact (posSemidef_ptrace hS (Matrix.le_iff.1 h1)).smul (inv_nonneg.2 hc.le)

/-- Energy terms on the site type `↥Λ` from local operators `0 ≤ B_i ≤ 1` on `S_i ⊆ Λ`. -/
noncomputable def domainTerms {N : ℕ} (S : Fin N → Finset σ) (hS : ∀ i, S i ⊆ Λ)
    (B : ∀ i, Matrix (Reg (fun _ : σ => Fin q) (S i)) (Reg (fun _ : σ => Fin q) (S i)) ℂ)
    (h0 : ∀ i, 0 ≤ B i) (h1 : ∀ i, B i ≤ 1) : EnergyTerms Λ (fun _ => q) (Fin N) where
  support i := (S i).subtype (· ∈ Λ)
  op i := (B i).submatrix (subtypeEquiv (hS i)) (subtypeEquiv (hS i))
  nonneg i := by
    rw [Matrix.nonneg_iff_posSemidef]
    exact ((Matrix.nonneg_iff_posSemidef).1 (h0 i)).submatrix _
  le_one i := by
    rw [Matrix.le_iff, ← submatrix_one_equiv (subtypeEquiv (hS i))]
    exact (Matrix.le_iff.1 (h1 i)).submatrix _

variable {N : ℕ} (S : Fin N → Finset σ) (hS : ∀ i, S i ⊆ Λ)
  (B : ∀ i, Matrix (Reg (fun _ : σ => Fin q) (S i)) (Reg (fun _ : σ => Fin q) (S i)) ℂ)
  (h0 : ∀ i, 0 ≤ B i) (h1 : ∀ i, B i ≤ 1)

theorem term_domainTerms (i : Fin N) :
    (domainTerms S hS B h0 h1).term i = extendId (hS i) (B i) :=
  localLift_subtype (hS i) (B i)

theorem budget_domainTerms (Q : Finset Λ) :
    budget (domainTerms S hS B h0 h1) Q = 1 + ∑ i ∈ univ.filter (fun i =>
      (S i ∩ up Q).Nonempty ∧ (S i ∩ (Λ \ up Q)).Nonempty),
        Real.log (Real.exp 1 * (q : ℝ) ^ #(S i)) ^ 2 := by
  unfold budget
  congr 1
  refine sum_congr (filter_congr fun i _ => ?_) fun i _ => ?_
  · exact and_congr (subtype_inter_nonempty_iff _ _) (subtype_sdiff_nonempty_iff _ _)
  · change Real.log (Real.exp 1 * (Fintype.card (RegionConfig (fun _ : Λ => q)
      ((S i).subtype (· ∈ Λ))) : ℝ)) ^ 2 = _
    rw [card_regionConfig_subtype (hS i)]
    push_cast
    rfl

end Domain

/-! ## D9.3 The truncated system -/

section Truncation

variable {σ : Type u} [DecidableEq σ] (G : SimpleGraph σ) [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
theorem truncatedSupport_subset (Λ S₀ : Finset σ) (r₀ : ℕ) (a : σ) :
    truncatedSupport G Λ S₀ r₀ a ⊆ Λ := by
  unfold truncatedSupport
  split_ifs
  exacts [component_subset G Λ a, graphNbhd_subset G Λ _ _]

omit [DecidableRel G.Adj] in
theorem isSupportedOn_of_eq {loc : σ → Type*}
    [∀ i, DecidableEq (loc i)] {S S' T : Finset σ} (h : S = S') (hS : S ⊆ T) (hS' : S' ⊆ T)
    {B : Matrix (Reg loc T) (Reg loc T) ℂ} (hB : OpenAI.IsSupportedOn hS' B) :
    OpenAI.IsSupportedOn hS B := by
  subst h; exact hB

omit [DecidableRel G.Adj] in
/-- D4.11. The truncated constraint `h̃_i` is supported in the truncated support `X̃_i`. -/
theorem isSupportedOn_truncated {q : ℕ} {Λ S₀ : Finset σ} {r₀ : ℕ} {a : σ}
    {k : Matrix (Reg (fun _ : σ => Fin q) Λ) (Reg (fun _ : σ => Fin q) Λ) ℂ}
    (hk : OpenAI.IsSupportedOn (component_subset G Λ a) k) :
    OpenAI.IsSupportedOn (truncatedSupport_subset G Λ S₀ r₀ a) (truncated G Λ S₀ r₀ a k) := by
  by_cases h : setDist G Λ S₀ a = ⊤
  · rw [show truncated G Λ S₀ r₀ a k = k from if_pos h]
    exact isSupportedOn_of_eq (if_pos h) _ _ hk
  · rw [show truncated G Λ S₀ r₀ a k =
      E G Λ a (radius r₀ (setDist G Λ S₀ a).toNat) k from if_neg h]
    exact isSupportedOn_of_eq (if_neg h) _ _ (isSupportedOn_E Λ a _ k)

/-- D9.3. `|S₀| ≤ |T| + nL ≤ (C_T + 1) n²` for `S₀ = A ∩ T_L`, `L ≤ n`. -/
theorem card_S₀_le {Λ A : Finset σ} (hA : A ⊆ Λ) {dep : σ → ℕ} {CT : ℝ} {n L r : ℕ}
    (hT : TestGeometry G Λ A dep CT n L r) (hL : L ≤ n) :
    (#(A.filter fun x => dep x ≤ L) : ℝ) ≤ (CT + 1) * (n : ℝ) ^ 2 := by
  have hsub : A.filter (fun x => dep x ≤ L) ⊆
      (range (L + 1)).biUnion fun j => Λ.filter fun x => dep x = j := by
    intro x hx
    rw [mem_filter] at hx
    exact mem_biUnion.2 ⟨dep x, mem_range.2 (Nat.lt_succ_of_le hx.2),
      mem_filter.2 ⟨hA hx.1, rfl⟩⟩
  have h1 := (card_le_card hsub).trans card_biUnion_le
  rw [sum_range_succ'] at h1
  have h2 : ∑ j ∈ range L, #(Λ.filter fun x => dep x = j + 1) ≤ L * n := by
    simpa using sum_le_sum fun j hj => hT.card_row (j + 1) (by omega)
      (Nat.succ_le_of_lt (mem_range.1 hj))
  have h3 : (#(A.filter fun x => dep x ≤ L) : ℝ) ≤
      (L * n : ℕ) + #(Λ.filter fun x => dep x = 0) := by
    exact_mod_cast h1.trans (Nat.add_le_add_right h2 _)
  have h4 : ((L * n : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
    rw [sq]; push_cast
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hL) (Nat.cast_nonneg _)
  linarith [hT.card_target]

/-- D4.14 (Proposition 4.5, last clause). The cut budget of a region `X ⊆ S₀` with
`|∂_Λ X| ≤ C₂ n D`, `D ≥ 1`, is `≤ C n D (log n)^{6 m₀}`, uniformly in `Λ, S₀, X` and the
anchors. -/
def CutBudgetBound (q R : ℕ) (C₁ : ℝ) (m₀ : ℕ) : Prop :=
  ∀ C₂ : ℝ, 0 ≤ C₂ → ∃ CD : ℝ, ∀ (Λ S₀ X : Finset σ) (a : Finset σ → σ) (n D : ℝ),
    (∀ Y ∈ supports G Λ R, a Y ∈ Y) → X ⊆ S₀ → 2 ≤ n → 1 ≤ D →
    (#(edgeBoundary G Λ X) : ℝ) ≤ C₂ * n * D →
    cutBudget G q Λ S₀ R ⌈C₁ * Real.log n ^ 2⌉₊ a X ≤ CD * n * D * Real.log n ^ (6 * m₀)

/-- D9.3. The truncated system of D4.11 at `S₀ = A ∩ T_L` (`A.filter (dep ≤ L)`), radius
`r₀ = ⌈C₁ (log n)²⌉`: `Ω̃` on the site type `↥Λ`, `H̃ = ∑_i h̃_i` presented as energy terms
`0 ≤ h̃_i ≤ 1` with designated supports `X̃_i`, anchors `a_i ∈ X_i`, `Ẽ₀ ≤ n^{-1000}`,
`g̃ = g/2`, the trace distance `½‖|Ω̃⟩⟨Ω̃| - |Ω⟩⟨Ω|‖₁ ≤ √(2 n^{-1000}/g)`, the Lemma 3.1
budget of each cut `Q` equal to the cut budget `𝓑_Q` of D4.11, and the crossing facts of
Proposition 4.5 for `X ⊆ S₀`. -/
structure TruncatedSystem (q : ℕ) [NeZero q] (R : ℕ) (g C₁ Cb : ℝ) (m₀ n L : ℕ)
    (Λ : Finset σ) (Ω : Reg (fun _ : σ => Fin q) Λ → ℂ) (hΩ : star Ω ⬝ᵥ Ω = 1)
    (A : Finset σ) (dep : σ → ℕ) where
  /-- `Ω̃`, `H̃`, `Ẽ₀`, `g̃`. -/
  Dt : PhysData (fun _ : Λ => q)
  /-- The number of labels `i`. -/
  N : ℕ
  /-- The energy terms `h̃_i` on their designated supports `X̃_i`. -/
  Et : EnergyTerms Λ (fun _ => q) (Fin N)
  /-- The anchors `a_i`. -/
  a : Finset σ → σ
  H_eq : Dt.H = ∑ i, Et.term i
  E₀_le : Dt.E₀ ≤ (n : ℝ) ^ (-1000 : ℝ)
  g_eq : Dt.g = g / 2
  traceDist_le : traceDist (pureState Dt.Ω Dt.norm_Ω) (pureState Ω hΩ) ≤
    √(2 * (n : ℝ) ^ (-1000 : ℝ) / g)
  anchor : ∀ Y ∈ supports G Λ R, a Y ∈ Y
  /-- The labels `i` are the admissible supports, with designated supports `X̃_i`. -/
  support_eq : ∃ e : Fin N ≃ supports G Λ R, ∀ i, Et.support i =
    (truncatedSupport G Λ (A.filter fun x => dep x ≤ L) (r₀ C₁ n) (a (e i))).subtype (· ∈ Λ)
  budget_eq : ∀ Q : Finset Λ,
    budget Et Q = cutBudget G q Λ (A.filter fun x => dep x ≤ L) R (r₀ C₁ n) a (up Q)
  crossing : ∀ X ⊆ A.filter (fun x => dep x ≤ L),
    (∀ Y ∈ crossingLabels G Λ (A.filter fun x => dep x ≤ L) R (r₀ C₁ n) a X,
      truncatedSupport G Λ (A.filter fun x => dep x ≤ L) (r₀ C₁ n) (a Y) =
        ball G Λ (a Y) (r₀ C₁ n)) ∧
    (#(crossingLabels G Λ (A.filter fun x => dep x ≤ L) R (r₀ C₁ n) a X) : ℝ) ≤
      Cb * #(edgeBoundary G Λ X) * ((r₀ C₁ n : ℝ) + 1) ^ m₀ ∧
    (∀ Y ∈ crossingLabels G Λ (A.filter fun x => dep x ≤ L) R (r₀ C₁ n) a X,
      Real.log ((q : ℝ) ^ #(truncatedSupport G Λ (A.filter fun x => dep x ≤ L) (r₀ C₁ n)
        (a Y))) ≤ Cb * ((r₀ C₁ n : ℝ) + 1) ^ m₀) ∧
    cutBudget G q Λ (A.filter fun x => dep x ≤ L) R (r₀ C₁ n) a X ≤
      Cb * (1 + #(edgeBoundary G Λ X)) * ((r₀ C₁ n : ℝ) + 1) ^ (3 * m₀)

/-- D9.3 (`scanner:test-geometry`, the truncated system). Under the test geometry with
`L ≤ n`, `S₀ = A ∩ T_L` has `|S₀| ≤ |T| + nL ≤ (C_T + 1) n²`, so Proposition 4.5 applies with
`C₀ = C_T + 1`, `s = 2`: there are `g = Δ/c_* > 0`, `C₁ > 0` and `C_b ≥ 0`, depending only on
`q, R, J, Δ`, the growth data and `C_T`, such that the truncated system `Ω̃, H̃ = ∑ h̃_i`,
`Ẽ₀ ≤ n^{-1000}`, `g̃ = g/2` exists, with the crossing facts of Proposition 4.5 and its uniform
cut-budget bound `𝓑_X ≤ C n D (log n)^{6 m₀}` for `b_X ≤ C₂ n D`. -/
theorem step_9_3 [Nonempty σ] (V : ℕ → ℕ)
    (hV : ∀ (Λ : Finset σ) (x : σ) (r : ℕ), #(ball G Λ x r) ≤ V r) {K₀ : ℝ} (hK₀ : 0 ≤ K₀)
    (m₀ : ℕ) (hVpoly : ∀ r : ℕ, (V r : ℝ) ≤ K₀ * (r + 1) ^ m₀) (q : ℕ) [NeZero q] (R : ℕ)
    (J : ℝ) {Δ : ℝ} (hΔ : 0 < Δ) {CT : ℝ} (hCT : 0 ≤ CT) :
    ∃ g C₁ Cb : ℝ, 0 < g ∧ 0 < C₁ ∧ 0 ≤ Cb ∧ CutBudgetBound G q R C₁ m₀ ∧
    ∀ n L : ℕ, 2 ≤ n → L ≤ n →
    ∀ (Λ : Finset σ)
      (Φ : (X : Finset σ) → Matrix (Reg (fun _ : σ => Fin q) X) (Reg (fun _ : σ => Fin q) X) ℂ),
      IsAdmissible G Λ R J Φ →
    ∀ (Ω : Reg (fun _ : σ => Fin q) Λ → ℂ) (hΩ : star Ω ⬝ᵥ Ω = 1) (E₀ : ℝ),
      hamiltonian Λ Φ *ᵥ Ω = (E₀ : ℂ) • Ω → HasGlobalGap (hamiltonian Λ Φ) Ω E₀ Δ →
    ∀ A : Finset σ, A ⊆ Λ → ∀ (dep : σ → ℕ) (r : ℕ), TestGeometry G Λ A dep CT n L r →
      Nonempty (TruncatedSystem G q R g C₁ Cb m₀ n L Λ Ω hΩ A dep) := by
  -- D4.11 (Proposition 4.5) with `C₀ = C_T + 1`, `s = 2`
  obtain ⟨cstar, hcs, C, c, hc, C₁, hC₁, Cb, hCb, hP, hcut⟩ :=
    prop_4_5 G V hV hK₀ m₀ hVpoly (Nat.one_le_iff_ne_zero.2 (NeZero.ne q)) R J hΔ
      (by linarith : (0 : ℝ) ≤ CT + 1) (by norm_num : (0 : ℝ) ≤ 2)
  refine ⟨Δ / cstar, C₁, Cb, div_pos hΔ hcs, hC₁, hCb, hcut, ?_⟩
  intro n L hn hL Λ Φ hΦ Ω hΩ E₀ hHΩ hgap A hA dep r hT
  set a : Finset σ → σ := fun X => if h : X.Nonempty then h.choose else Classical.arbitrary σ
  have ha : ∀ X ∈ supports G Λ R, a X ∈ X := fun X hX => by
    have hne : X.Nonempty := (mem_filter.1 hX).2.1
    simp only [a, dif_pos hne]
    exact hne.choose_spec
  obtain ⟨k, ⟨hk, -, -, -, hsupp⟩, hn'⟩ := hP Λ Φ hΦ Ω hΩ E₀ hHΩ hgap a ha
  set S₀ := A.filter fun x => dep x ≤ L
  -- D9.3: `|S₀| ≤ (C_T + 1) n²`
  have hS₀ : (#S₀ : ℝ) ≤ (CT + 1) * (n : ℝ) ^ (2 : ℝ) := by
    rw [Real.rpow_two]; exact card_S₀_le G hA hT hL
  obtain ⟨h1, -, ⟨Et₀, Ωt, hΩt, hEig, -, hE1, hgap2, -, -, -, htd⟩, hcross⟩ :=
    hn' n (by exact_mod_cast hn) S₀ hS₀
  -- the labels `i`, enumerated
  set e := (supports G Λ R).equivFin
  set Xs : Fin #(supports G Λ R) → Finset σ := fun i => (e.symm i).1
  have hXs (i) : Xs i ∈ supports G Λ R := (e.symm i).2
  have hop (i) := exists_op (truncatedSupport_subset G Λ S₀ (r₀ C₁ n) (a (Xs i)))
    (isSupportedOn_truncated G (hsupp _ (hXs i))) (h1 _ (hXs i)).1 (h1 _ (hXs i)).2
  choose B hB hB0 hB1 using hop
  set Et := domainTerms (fun i => truncatedSupport G Λ S₀ (r₀ C₁ n) (a (Xs i)))
    (fun i => truncatedSupport_subset G Λ S₀ (r₀ C₁ n) (a (Xs i))) B hB0 hB1
  refine ⟨{
    Dt := {
      Ω := Ωt
      H := ∑ X ∈ supports G Λ R, truncated G Λ S₀ (r₀ C₁ n) (a X) (k X)
      E₀ := Et₀
      g := Δ / cstar / 2
      norm_Ω := hΩt
      nonneg := sum_nonneg fun X hX => (h1 X hX).1
      ground := hEig
      gap_pos := by positivity
      gap := hgap2 }
    N := #(supports G Λ R)
    Et := Et
    a := a
    H_eq := ?_
    E₀_le := hE1.trans (min_le_left _ _)
    g_eq := rfl
    traceDist_le := htd.trans (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)) (div_pos hΔ hcs).le))
    anchor := ha
    support_eq := ⟨e.symm, fun _ => rfl⟩
    budget_eq := fun Q => ?_
    crossing := hcross }⟩
  · -- `H̃ = ∑_i h̃_i`
    change ∑ X ∈ supports G Λ R, truncated G Λ S₀ (r₀ C₁ n) (a X) (k X) = ∑ i, Et.term i
    rw [← sum_coe_sort (supports G Λ R), ← e.symm.sum_comp]
    exact sum_congr rfl fun i _ => (hB i).trans (term_domainTerms _ _ B hB0 hB1 i).symm
  · -- the Lemma 3.1 budget is the cut budget of D4.11
    rw [budget_domainTerms, cutBudget, crossingLabels, sum_filter, sum_filter]
    congr 1
    rw [← sum_coe_sort (supports G Λ R), ← e.symm.sum_comp]

end Truncation


/-! ## D9.9.1 The transfer `Ω → Ω̃` -/

section Transfer

theorem log_exp_mul_card_nonneg (m : ℕ) : 0 ≤ Real.log (Real.exp 1 * m) := by
  rcases Nat.eq_zero_or_pos m with h | h
  · simp [h]
  · exact Real.log_nonneg (by
      have : (1 : ℝ) ≤ m := by exact_mod_cast h
      nlinarith [Real.add_one_le_exp (1 : ℝ)])

section Continuity

variable {σ : Type*} [DecidableEq σ] {loc : σ → Type*} [∀ i, Fintype (loc i)]
  [∀ i, DecidableEq (loc i)] {U X Y : Finset σ}

/-- D2.4 (Lemma 2.1) for `S(X|Y)`, with the trace distance of the full states. -/
theorem abs_condEntropy_sub_le (ρ τ : MState (Reg loc U) ℂ) (hX : X ⊆ U) (hY : Y ⊆ U)
    (hXY : Disjoint X Y) :
    |(ρ.toSubState.regionEntropy (union_subset hX hY) - ρ.toSubState.regionEntropy hY) -
        (τ.toSubState.regionEntropy (union_subset hX hY) - τ.toSubState.regionEntropy hY)| ≤
      4 * √(traceDist ρ τ) * Real.log (Real.exp 1 * Fintype.card (Reg loc X)) := by
  refine ((lemma_2_1 U X Y hX hY hXY ρ τ).2).trans ?_
  gcongr
  · exact log_exp_mul_card_nonneg _
  · exact SubState.D₁_restrict_le _ _ _

/-- D2.4 (Lemma 2.1) for `S(X)`. -/
theorem abs_regionEntropy_sub_le (ρ τ : MState (Reg loc U) ℂ) (hX : X ⊆ U) :
    |ρ.toSubState.regionEntropy hX - τ.toSubState.regionEntropy hX| ≤
      4 * √(traceDist ρ τ) * Real.log (Real.exp 1 * Fintype.card (Reg loc X)) := by
  have h := abs_condEntropy_sub_le ρ τ hX (empty_subset U) (disjoint_empty_right X)
  have he (ω : MState (Reg loc U) ℂ) : ω.toSubState.regionEntropy (empty_subset U) = 0 := by
    rw [SubState.regionEntropy_empty, ω.tr_eq_one, Real.negMulLog_one]
  have hu (ω : MState (Reg loc U) ℂ) : ω.toSubState.regionEntropy
      (union_subset hX (empty_subset U)) = ω.toSubState.regionEntropy hX :=
    ω.toSubState.regionEntropy_congr (union_empty X) _ _
  rwa [he, he, hu, hu, sub_zero, sub_zero] at h

/-- D2.4 (Lemma 2.1) for `I(X : Y) = S(X) - S(X|Y)`: only `d_X` enters. -/
theorem abs_mutualInfo_sub_le (ρ τ : MState (Reg loc U) ℂ) (hX : X ⊆ U) (hY : Y ⊆ U)
    (hXY : Disjoint X Y) :
    |ρ.toSubState.mutualInfo hX hY - τ.toSubState.mutualInfo hX hY| ≤
      8 * √(traceDist ρ τ) * Real.log (Real.exp 1 * Fintype.card (Reg loc X)) := by
  have h1 := abs_regionEntropy_sub_le ρ τ hX
  have h2 := abs_condEntropy_sub_le ρ τ hX hY hXY
  rw [SubState.mutualInfo_def, SubState.mutualInfo_def]
  calc _ = |(ρ.toSubState.regionEntropy hX - τ.toSubState.regionEntropy hX) -
        ((ρ.toSubState.regionEntropy (union_subset hX hY) - ρ.toSubState.regionEntropy hY) -
        (τ.toSubState.regionEntropy (union_subset hX hY) - τ.toSubState.regionEntropy hY))| := by
        ring_nf
    _ ≤ _ := (abs_sub _ _).trans (by linarith)

end Continuity

theorem four_root_le {c g t : ℝ} (hc : 0 ≤ c) (hg : 0 < g) (ht : 0 ≤ t)
    (hε : 2 * c ^ 4 * t ≤ g) : c * √(√(2 * t ^ 5 / g)) ≤ t := by
  have hx : 0 ≤ 2 * t ^ 5 / g := by positivity
  have h4 : (c * √(√(2 * t ^ 5 / g))) ^ 4 = c ^ 4 * (2 * t ^ 5 / g) := by
    rw [mul_pow, show (√(√(2 * t ^ 5 / g))) ^ 4 = ((√(√(2 * t ^ 5 / g))) ^ 2) ^ 2 by ring,
      Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hx]
  refine (pow_le_pow_iff_left₀ (by positivity) ht (by norm_num : (4 : ℕ) ≠ 0)).1 ?_
  rw [h4, mul_div_assoc', div_le_iff₀ hg]
  nlinarith [pow_nonneg ht 4]

theorem eventually_rpow_neg_le {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → (n : ℝ) ^ (-a) ≤ ε := by
  have h := (tendsto_rpow_neg_atTop ha).comp tendsto_natCast_atTop_atTop
  exact Filter.eventually_atTop.1 (h.eventually (Iic_mem_nhds hε))

variable {σ : Type u} [DecidableEq σ]

theorem card_reg_fin (q : ℕ) (Z : Finset σ) :
    (Fintype.card (Reg (fun _ : σ => Fin q) Z) : ℝ) = (q : ℝ) ^ #Z := by
  rw [Fintype.card_pi, prod_const, card_univ, Fintype.card_coe, Fintype.card_fin]
  push_cast; rfl

theorem log_card_up_le {Λ : Finset σ} (q : ℕ) [NeZero q] (Q : Finset Λ) :
    Real.log (Real.exp 1 * Fintype.card (Reg (fun _ : σ => Fin q) (up Q))) ≤
      (1 + Real.log q) * (1 + #Q) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hl := Real.log_nonneg hq
  rw [card_reg_fin, up, card_map, Real.log_mul (Real.exp_pos 1).ne' (by positivity),
    Real.log_exp, Real.log_pow]
  nlinarith [(Nat.cast_nonneg #Q : (0 : ℝ) ≤ #Q)]

/-- D9.9.1 (transfer `Ω → Ω̃`). For `n ≥ n₀` (depending on `q` and `g`), a physical system
`Ω̃` on `↥Λ` whose trace distance to `Ω` is `≤ √(2 n^{-1000}/g)` (Proposition 4.5) has
`|S_{Ω̃}(Q) - S_Ω(Q)| ≤ n^{-200}(1 + |Q|)` and `|I_{Ω̃}(Q:Q') - I_Ω(Q:Q')| ≤ n^{-200}(1 + |Q|)`
for all `Q` and disjoint `Q, Q'`: Lemma 2.1 with `δ = O(n^{-500})` and `log d_Q ≤ |Q| log q`. -/
theorem step_9_9_1 (q : ℕ) [NeZero q] {g : ℝ} (hg : 0 < g) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ (Λ : Finset σ) (Ω : Reg (fun _ : σ => Fin q) Λ → ℂ)
      (hΩ : star Ω ⬝ᵥ Ω = 1) (Dt : PhysData (fun _ : Λ => q)),
      traceDist (pureState Dt.Ω Dt.norm_Ω) (pureState Ω hΩ) ≤
        √(2 * (n : ℝ) ^ (-1000 : ℝ) / g) →
      (∀ Q : Finset Λ, |Dt.S Q - (pureState Ω hΩ).regionEntropy (up_subset Q)| ≤
        (n : ℝ) ^ (-200 : ℝ) * (1 + #Q)) ∧
      ∀ Q Q' : Finset Λ, Disjoint Q Q' →
        |Dt.I Q Q' - (pureState Ω hΩ).mutualInfo (up_subset Q) (up_subset Q')| ≤
          (n : ℝ) ^ (-200 : ℝ) * (1 + #Q) := by
  set c := 8 * (1 + Real.log q)
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hl := Real.log_nonneg hq
  have hc : 0 < c := by positivity
  obtain ⟨n₀, hn₀⟩ := eventually_rpow_neg_le (a := 200) (by norm_num)
    (by positivity : 0 < g / (2 * c ^ 4))
  refine ⟨n₀, fun n hn Λ Ω hΩ Dt hδ => ?_⟩
  set ψ : Reg (fun _ : σ => Fin q) Λ → ℂ := Dt.Ω
  set δ := traceDist (pureState ψ Dt.norm_Ω) (pureState Ω hΩ)
  set t := (n : ℝ) ^ (-200 : ℝ)
  have ht : 0 ≤ t := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have h5 : (n : ℝ) ^ (-1000 : ℝ) = t ^ 5 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]; norm_num
  -- D9.9.1: `δ ≤ √(2 ε_n / g) ≤ √(2 n^{-1000} / g)` (Proposition 4.5), so `c √δ ≤ n^{-200}`
  have hsmall : c * √δ ≤ t := by
    refine (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hδ) hc.le).trans ?_
    rw [h5]
    refine four_root_le hc.le hg ht ?_
    have := hn₀ n hn
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hδ0 : 0 ≤ √δ := Real.sqrt_nonneg _
  have hS (Q : Finset Λ) : Dt.S Q = (pureState ψ Dt.norm_Ω).toSubState.regionEntropy
      (up_subset Q) :=
    regionEntropy_comp_univEquiv (loc := fun _ : σ => Fin q) ψ Dt.norm_Ω Dt.norm_Ω_univEquiv Q
  have hI (Q Q' : Finset Λ) : Dt.I Q Q' = (pureState ψ Dt.norm_Ω).toSubState.mutualInfo
      (up_subset Q) (up_subset Q') :=
    mutualInfo_comp_univEquiv (loc := fun _ : σ => Fin q) ψ Dt.norm_Ω Dt.norm_Ω_univEquiv Q Q'
  constructor
  · -- D9.9.1: Lemma 2.1 for `S(Q)`, `log (e d_Q) ≤ (1 + log q)(1 + |Q|)`
    intro Q
    rw [hS]
    have h1 := abs_regionEntropy_sub_le (pureState ψ Dt.norm_Ω) (pureState Ω hΩ) (up_subset Q)
    have h2 := log_card_up_le q Q
    have h3 := mul_nonneg (mul_nonneg hδ0 (by positivity : (0 : ℝ) ≤ 1 + Real.log q))
      (by positivity : (0 : ℝ) ≤ 1 + #Q)
    calc _ ≤ 4 * √δ * ((1 + Real.log q) * (1 + #Q)) := h1.trans (by gcongr)
      _ ≤ c * √δ * (1 + #Q) := by simp only [c]; nlinarith
      _ ≤ t * (1 + #Q) := by gcongr
  · -- D9.9.1: Lemma 2.1 for `S(Q)` and `S(Q | Q')`
    intro Q Q' hQQ'
    rw [hI]
    have h1 := abs_mutualInfo_sub_le (pureState ψ Dt.norm_Ω) (pureState Ω hΩ) (up_subset Q)
      (up_subset Q') ((Finset.disjoint_map _).2 hQQ')
    have h2 := log_card_up_le q Q
    calc _ ≤ 8 * √δ * ((1 + Real.log q) * (1 + #Q)) := h1.trans (by gcongr)
      _ = c * √δ * (1 + #Q) := by simp only [c]; ring
      _ ≤ t * (1 + #Q) := by gcongr

end Transfer

end AreaLaw.Scanner
