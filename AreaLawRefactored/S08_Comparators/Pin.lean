import AreaLawRefactored.S08_Comparators.Interfaces

/-!
# §8.2 The Bell pin, the pin norm and the pinned metric (D8.14–D8.16)

Digest `digest/08-comparators.md` D8.14–D8.16, paper `paper/sections/07-comparators.tex`
283–318. Arbitrary finite site type, arbitrary local dimensions; no geometry. `𝖯` is
`pinProj`, the tensor power of the one-copy pin `𝖯₁ = |B_{XC}⟩⟨B_{XC}| ⊗ 1` (`pin1`).
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Filter Topology Arealaw Entropy PermutationRepresentation

namespace AreaLaw.Comparators

universe u v

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ} {D : PhysData n} {X : Finset σ}

/-! ## The factors `XC` -/

omit [Fintype σ] [DecidableEq σ] in
theorem mem_physReg {v : σ} {Q : Finset σ} : Site.phys v ∈ physReg Q ↔ v ∈ Q :=
  Finset.mem_map' _

omit [Fintype σ] in
theorem phys_mem_XC {v : σ} : Site.phys v ∈ XC X ↔ v ∈ X := by
  rw [XC, Finset.mem_insert]
  simp only [reduceCtorEq, false_or]
  exact mem_physReg

omit [Fintype σ] in
theorem C_mem_XC : (Site.C : Site σ) ∈ XC X := by simp [XC]

omit [Fintype σ] in
theorem R_not_mem_XC : (Site.R : Site σ) ∉ XC X := by simp [XC, physReg]

theorem BXC_congr (E : TypicalSet D X) {x y : SiteConfig (dims n E.d)}
    (h : ∀ f ∈ XC X, x f = y f) : BXC E x = BXC E y := by
  have hC : x .C = y .C := h _ C_mem_XC
  have hX : restrictX (X := X) (physPart x) = restrictX (physPart y) :=
    funext fun v => h _ (phys_mem_XC.2 v.2)
  simp only [BXC, hC, hX]

/-- The configuration agreeing with `x` off `XC`, with `C`-value `c` and `X`-part `z`. -/
def glueXC {d : ℕ} (x : SiteConfig (dims n d)) (c : Fin d) (z : Reg (fun v => Fin (n v)) X) :
    SiteConfig (dims n d) := fun f =>
  match f with
  | .phys v => if h : v ∈ X then z ⟨v, h⟩ else x (.phys v)
  | .C => c
  | .R => x .R

/-- A sum over the configurations agreeing with `x` off `XC` is a sum over `C × X`. -/
theorem sum_agree {d : ℕ} (x : SiteConfig (dims n d)) (φ : SiteConfig (dims n d) → ℂ) :
    ∑ y, (if ∀ f ∉ XC X, x f = y f then φ y else 0) =
      ∑ p : Fin d × Reg (fun v => Fin (n v)) X, φ (glueXC x p.1 p.2) := by
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun y => (y .C, fun v => y (.phys v.1)))
    (fun p => glueXC x p.1 p.2) (by simp) ?_ ?_ ?_ ?_
  · intro p _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro f hf
    cases f with
    | phys v =>
      have hv : v ∉ X := fun h => hf (phys_mem_XC.2 h)
      simp [glueXC, hv]
    | C => exact absurd C_mem_XC hf
    | R => rfl
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    funext f
    cases f with
    | phys v =>
      by_cases hv : v ∈ X
      · simp [glueXC, hv]
      · simp [glueXC, hv, hy _ (fun h => hv (phys_mem_XC.1 h))]
    | C => rfl
    | R => exact hy _ R_not_mem_XC
  · intro p _
    ext v
    · rfl
    · simp [glueXC, v.2]
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    congr 1
    funext f
    cases f with
    | phys v =>
      by_cases hv : v ∈ X
      · simp [glueXC, hv]
      · simp [glueXC, hv, hy _ (fun h => hv (phys_mem_XC.1 h))]
    | C => rfl
    | R => exact (hy _ R_not_mem_XC).symm

omit [Fintype σ] in
@[simp] theorem glueXC_C {d : ℕ} (x : SiteConfig (dims n d)) (c : Fin d)
    (z : Reg (fun v => Fin (n v)) X) : glueXC x c z .C = c := rfl

omit [Fintype σ] in
@[simp] theorem glueXC_R {d : ℕ} (x : SiteConfig (dims n d)) (c : Fin d)
    (z : Reg (fun v => Fin (n v)) X) : glueXC x c z .R = x .R := rfl

omit [Fintype σ] in
@[simp] private theorem restrictX_replaceX (x : SiteConfig n)
    (z : Reg (fun v => Fin (n v)) X) :
    restrictX (replaceX x z) = z :=
  funext fun v => by simp [restrictX, replaceX, v.2]

/-! ## The one-copy pin -/

/-- `𝖯₁ = |B_{XC}⟩⟨B_{XC}| ⊗ 1` on one copy of `𝒱`. -/
noncomputable def pin1 (E : TypicalSet D X) :
    Matrix (SiteConfig (dims n E.d)) (SiteConfig (dims n E.d)) ℂ :=
  fun x y => BXC E x * star (BXC E y) * if ∀ f ∉ XC X, x f = y f then 1 else 0

theorem pinProj_eq_tensorPow (E : TypicalSet D X) (k : ℕ) :
    pinProj E k = TensorPower.tensorPow (k := k) (pin1 E) := by
  ext x y
  rw [TensorPower.tensorPow_apply]
  simp only [pinProj, pin1, Finset.prod_mul_distrib, Finset.prod_boole, Finset.mem_univ,
    true_implies]

theorem p_pos (E : TypicalSet D X) {i} (hi : i ∈ E.E) : 0 < D.p X i :=
  (Real.exp_pos _).trans_le (E.lower i hi)

theorem z_pos (E : TypicalSet D X) : 0 < E.z :=
  Finset.sum_pos (fun _ hi => p_pos E hi) E.nonempty

theorem BXC_glueXC (E : TypicalSet D X) (x : SiteConfig (dims n E.d)) (c : Fin E.d)
    (z : Reg (fun v => Fin (n v)) X) :
    BXC E (glueXC x c z) = ((Real.sqrt E.d)⁻¹ : ℝ) * schmidtX (D := D) (E.idx c).1 z := by
  change ((Real.sqrt E.d)⁻¹ : ℝ) * schmidtX (D := D) (E.idx c).1
    (restrictX (replaceX (physPart x) z)) = _
  rw [restrictX_replaceX]

theorem preVec_glueXC {d : ℕ} (x : SiteConfig (dims n d)) (c : Fin d)
    (z : Reg (fun v => Fin (n v)) X) :
    preVec D d (glueXC x c z) = D.Ω (replaceX (physPart x) z) * bell d c (x .R) := rfl

omit [Fintype σ] [DecidableEq σ] in
theorem sum_bell {d : ℕ} {β : Type*} [Fintype β] (r : Fin d) (F : Fin d → β → ℂ) :
    ∑ c, ∑ z, F c z * bell d c r = ((Real.sqrt d)⁻¹ : ℝ) * ∑ z, F r z := by
  simp only [bell, mul_ite, mul_zero]
  rw [Finset.sum_comm, Finset.mul_sum]
  simp [Finset.sum_ite_eq', mul_comm]

/-- D8.14.1. `𝖯₁(Ω̃ ⊗ Bell_{CR}) = (√z/d_*) B_{XC} ⊗ ψ`. -/
theorem step_8_14_1 (E : TypicalSet D X) :
    pin1 E *ᵥ preVec D E.d = ((Real.sqrt E.z : ℂ) / E.d) • fun x => BXC E x * ψ E x := by
  funext x
  have hd : (0 : ℝ) < E.d := by exact_mod_cast E.nonempty.card_pos
  have hp := p_pos E (E.idx (x .R)).2
  have hz := z_pos E
  have e : (pin1 E *ᵥ preVec D E.d) x = BXC E x *
      ∑ y, if ∀ f ∉ XC X, x f = y f then star (BXC E y) * preVec D E.d y else 0 := by
    simp only [mulVec, dotProduct, pin1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs <;> ring
  rw [e, sum_agree, Fintype.sum_prod_type]
  simp only [BXC_glueXC, preVec_glueXC, ← mul_assoc]
  rw [sum_bell (d := E.d) (x .R)]
  simp only [BXC, ψ, schmidtW, TypicalSet.p', Pi.smul_apply, smul_eq_mul, star_mul',
    Complex.star_def, Complex.conj_ofReal]
  have hs : ∀ (a : ℂ) (c : Reg (fun v => Fin (n v)) X → ℂ),
      ∑ z, a * c z * D.Ω (replaceX (physPart x) z) =
        a * ∑ z, c z * D.Ω (replaceX (physPart x) z) := fun a c => by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hs, Real.sqrt_div hp.le]
  generalize (∑ z : Reg (fun v => Fin (n v)) X,
    (starRingEnd ℂ) (schmidtX (D := D) (E.idx (x .R)).1 z) * D.Ω (replaceX (physPart x) z)) = S
  have hdd : ((Real.sqrt E.d : ℝ) : ℂ) * (Real.sqrt E.d : ℝ) = E.d := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hd.le]; simp
  have h1 : ((Real.sqrt E.d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hd).ne'
  have h2 : ((Real.sqrt (D.p X (E.idx (x .R))) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hp).ne'
  have h3 : ((Real.sqrt E.z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hz).ne'
  rw [← hdd]
  push_cast
  field_simp

omit [Fintype σ] [DecidableEq σ] in
theorem tensorVec_smul {Ω : Type*} (k : ℕ) (c : ℂ) (θ : Ω → ℂ) :
    TensorPower.tensorVec k (c • θ) = c ^ k • TensorPower.tensorVec k θ := by
  funext x
  simp [TensorPower.tensorVec, Finset.prod_mul_distrib, Finset.prod_const]

/-! ## Commutation with the pin -/

omit [Fintype σ] [DecidableEq σ] in
/-- A matrix invariant under the relabelling `φ g` commutes with `U(g)`. -/
theorem commute_permOp_of_invariant {G Y : Type*} [Group G] [Fintype Y] [DecidableEq Y]
    (φ : G →* Equiv.Perm Y) (g : G) {M : Matrix Y Y ℂ}
    (h : ∀ x y, M (φ g x) (φ g y) = M x y) : Commute (permOp φ g) M := by
  ext x y
  simp only [mul_apply, permOp_apply_apply]
  have h1 : ∑ z, (if φ g z = x then (1 : ℂ) else 0) * M z y = M ((φ g).symm x) y := by
    rw [← Equiv.sum_comp (φ g).symm]
    simp
  have h2 : ∑ z, M x z * (if φ g y = z then (1 : ℂ) else 0) = M x (φ g y) := by simp
  rw [h1, h2, ← h ((φ g).symm x) y, Equiv.apply_symm_apply]

omit [Fintype σ] in
theorem agree_copyPerm {d k : ℕ} (Q : Finset (Site σ)) (π : Equiv.Perm (Fin k))
    (x y : Transport.Config (dims n d) k) :
    (∀ j, ∀ f ∉ XC X, Replicas.copyPerm (fun f => Fin (dims n d f)) k Q π x j f =
        Replicas.copyPerm (fun f => Fin (dims n d f)) k Q π y j f) ↔
      ∀ j, ∀ f ∉ XC X, x j f = y j f := by
  simp only [Replicas.copyPerm_apply]
  constructor
  · intro h j f hf
    by_cases hQ : f ∈ Q
    · simpa [hQ] using h (π j) f hf
    · simpa [hQ] using h j f hf
  · intro h j f hf
    split_ifs
    · exact h _ f hf
    · exact h j f hf

/-- `𝖯` is invariant under the copy permutations of a region containing `XC` or disjoint from
it. -/
theorem pinProj_copyPerm (E : TypicalSet D X) {k : ℕ} {Q : Finset (Site σ)}
    (hQ : XC X ⊆ Q ∨ Disjoint Q (XC X)) (π : Equiv.Perm (Fin k))
    (x y : Transport.Config (dims n E.d) k) :
    pinProj E k (Replicas.copyPerm (fun f => Fin (dims n E.d f)) k Q π x)
        (Replicas.copyPerm (fun f => Fin (dims n E.d f)) k Q π y) = pinProj E k x y := by
  simp only [pinProj, agree_copyPerm]
  congr 1
  rcases hQ with hQ | hQ
  · have hb : ∀ (x : Transport.Config (dims n E.d) k) j,
        BXC E (Replicas.copyPerm (fun f => Fin (dims n E.d f)) k Q π x j) = BXC E (x (π⁻¹ j)) :=
      fun x j => BXC_congr E fun f hf => by simp [hQ hf]
    simp only [hb]
    exact Equiv.prod_comp π⁻¹ fun j => BXC E (x j) * star (BXC E (y j))
  · have hb : ∀ (x : Transport.Config (dims n E.d) k) j,
        BXC E (Replicas.copyPerm (fun f => Fin (dims n E.d f)) k Q π x j) = BXC E (x j) :=
      fun x j => BXC_congr E fun f hf => by
        simp [Finset.disjoint_right.1 hQ hf]
    simp only [hb]

theorem commute_pinProj_labelObservable (E : TypicalSet D X) {k : ℕ} {Q : Finset (Site σ)}
    (hQ : XC X ⊆ Q ∨ Disjoint Q (XC X)) (g : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) :
    Commute (pinProj E k)
      (labelObservable (Replicas.copyPerm (fun f => Fin (dims n E.d f)) k Q) g) :=
  (commute_labelObservable_of_forall_commute _
    (fun π => commute_permOp_of_invariant _ π (pinProj_copyPerm E hQ π)) g).symm

theorem commute_pinProj_labelProj (E : TypicalSet D X) {k : ℕ} {Q : Finset (Site σ)}
    (hQ : XC X ⊆ Q ∨ Disjoint Q (XC X)) (l : IrrepLabel (Equiv.Perm (Fin k))) :
    Commute (pinProj E k) (labelProj (Replicas.copyPerm (fun f => Fin (dims n E.d f)) k Q) l) :=
  (commute_labelProj_of_forall_commute _
    (fun π => commute_permOp_of_invariant _ π (pinProj_copyPerm E hQ π)) l).symm

/-! ## D8.14 Bell pin -/

/-- D8.14 (`comparator:bell-pin`). `𝖯 pre_k = (√z/d_*)^k π^λ_R post_k`. -/
theorem step_8_14 (E : TypicalSet D X) (k : ℕ) (l : IrrepLabel (Equiv.Perm (Fin k))) :
    pinProj E k *ᵥ pre D E.d k l =
      ((Real.sqrt E.z / E.d) ^ k : ℂ) • (piR E.d k l *ᵥ post E k) := by
  -- D8.14.2: `π^λ_R` acts on `R`, disjoint from `XC`, so commutes with `𝖯`
  have hc : Commute (pinProj E k) (piR E.d k l) :=
    commute_pinProj_labelProj E (Or.inr (Finset.disjoint_singleton_left.2 R_not_mem_XC)) l
  rw [pre, mulVec_mulVec, hc.eq, ← mulVec_mulVec, pinProj_eq_tensorPow,
    TensorPower.tensorPow_mulVec_tensorVec,
    -- D8.14.1: one copy, then the tensor power
    step_8_14_1, tensorVec_smul, mulVec_smul, post]

/-! ## D8.15 Pin norm -/

theorem sum_star_mul_schmidtX (i : Reg (fun v => Fin (n v)) X) :
    ∑ w, star (schmidtX (D := D) i w) * schmidtX (D := D) i w = 1 := by
  have h := (D.isHermitian_ρ X).eigenvectorBasis.inner_eq_ite i i
  simp only [if_true] at h
  rw [← h, PiLp.inner_apply]
  exact Finset.sum_congr rfl fun w _ => by simp [schmidtX, mul_comm, Complex.mul_conj']

theorem pin1_mul_self (E : TypicalSet D X) : pin1 E * pin1 E = pin1 E := by
  have hd : (0 : ℝ) < E.d := by exact_mod_cast E.nonempty.card_pos
  ext x y
  have hn : ∑ p : Fin E.d × Reg (fun v => Fin (n v)) X,
      BXC E (glueXC x p.1 p.2) * star (BXC E (glueXC x p.1 p.2)) = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [BXC_glueXC, star_mul', Complex.star_def, Complex.conj_ofReal]
    have hsd : (((Real.sqrt E.d)⁻¹ : ℝ) : ℂ) * ((Real.sqrt E.d)⁻¹ : ℝ) = ((E.d : ℝ)⁻¹ : ℝ) := by
      rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hd.le]
    have e : ∀ c : Fin E.d, ∑ w, ((Real.sqrt E.d)⁻¹ : ℝ) * schmidtX (D := D) (E.idx c).1 w *
        (((Real.sqrt E.d)⁻¹ : ℝ) * (starRingEnd ℂ) (schmidtX (D := D) (E.idx c).1 w)) =
        ((E.d : ℝ)⁻¹ : ℝ) := fun c => by
      rw [← mul_one ((((E.d : ℝ)⁻¹ : ℝ) : ℂ)), ← sum_star_mul_schmidtX (D := D) (E.idx c).1,
        ← hsd, Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ => by rw [Complex.star_def]; ring
    have hd' : (E.d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    simp only [e, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  have e2 : (pin1 E * pin1 E) x y = BXC E x * star (BXC E y) *
      (if ∀ f ∉ XC X, x f = y f then 1 else 0) *
        ∑ z, (if ∀ f ∉ XC X, x f = z f then BXC E z * star (BXC E z) else 0) := by
    simp only [mul_apply, pin1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases h1 : ∀ f ∉ XC X, x f = z f
    · by_cases h3 : ∀ f ∉ XC X, x f = y f
      · have h2 : ∀ f ∉ XC X, z f = y f := fun f hf => (h1 f hf).symm.trans (h3 f hf)
        simp only [if_pos h1, if_pos h2, if_pos h3]
        ring
      · have h2 : ¬ ∀ f ∉ XC X, z f = y f := fun h2 => h3 fun f hf => (h1 f hf).trans (h2 f hf)
        simp only [if_pos h1, if_neg h2, if_neg h3]
        ring
    · simp only [if_neg h1]
      ring
  rw [e2, sum_agree, hn, mul_one]
  rfl

theorem isHermitian_pin1 (E : TypicalSet D X) : (pin1 E).IsHermitian := by
  ext x y
  simp only [conjTranspose_apply, pin1, star_mul', star_star]
  by_cases h : ∀ f ∉ XC X, x f = y f
  · simp only [if_pos h, if_pos (fun f hf => (h f hf).symm), star_one]
    ring
  · have h' : ¬ ∀ f ∉ XC X, y f = x f := fun h' => h fun f hf => (h' f hf).symm
    simp only [if_neg h, if_neg h', star_zero]
    ring

theorem pinProj_mul_self (E : TypicalSet D X) (k : ℕ) :
    pinProj E k * pinProj E k = pinProj E k := by
  rw [pinProj_eq_tensorPow, ← TensorPower.tensorPow_mul, pin1_mul_self]

theorem isHermitian_pinProj (E : TypicalSet D X) (k : ℕ) : (pinProj E k).IsHermitian := by
  rw [pinProj_eq_tensorPow, IsHermitian, TensorPower.conjTranspose_tensorPow,
    (isHermitian_pin1 E).eq]

omit [Fintype σ] [DecidableEq σ] in
/-- An orthogonal projection does not increase the norm: `‖𝖯 w‖² ≤ ‖w‖²`. -/
theorem re_star_mulVec_le {m : Type*} [Fintype m] {P : Matrix m m ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) (w : m → ℂ) :
    (star (P *ᵥ w) ⬝ᵥ (P *ᵥ w)).re ≤ (star w ⬝ᵥ w).re := by
  classical
  have hnn : ∀ u : m → ℂ, 0 ≤ (star u ⬝ᵥ u).re := fun u => by
    simp only [dotProduct, Pi.star_apply, Complex.re_sum]
    exact Finset.sum_nonneg fun i _ => by
      rw [Complex.star_def, Complex.conj_mul']; norm_cast; positivity
  have hsq : ∀ M : Matrix m m ℂ, M.IsHermitian → M * M = M →
      star (M *ᵥ w) ⬝ᵥ (M *ᵥ w) = star w ⬝ᵥ (M *ᵥ w) := fun M hM hMM => by
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hM.eq, hMM]
  have hQ : (1 - P).IsHermitian := by
    simp [IsHermitian, conjTranspose_sub, hP.eq]
  have hQQ : (1 - P) * (1 - P) = 1 - P := by
    rw [sub_mul, mul_sub, mul_sub, hPP]; simp
  have h := hnn ((1 - P) *ᵥ w)
  rw [hsq _ hQ hQQ, sub_mulVec, one_mulVec, dotProduct_sub, Complex.sub_re] at h
  rw [hsq _ hP hPP]
  linarith

omit [Fintype σ] [DecidableEq σ] in
private theorem commute_rpow_of_commute {m : Type*} [Fintype m] [DecidableEq m]
    {Z A : Matrix m m ℂ}
    (h : Commute Z A) (r : ℝ) : Commute Z (A ^ r) := by
  rw [CFC.rpow_def]
  exact (Commute.cfc_nnreal h.symm _).symm

omit [Fintype σ] [DecidableEq σ] in
/-- A matrix commuting with every leaf commutes with the root of a mean tree (no positivity
needed: the root is built from products and real powers of the leaves). -/
private theorem commute_eval_of_commute {ι m : Type*} [Fintype m] [DecidableEq m]
    {Z : Matrix m m ℂ}
    {A : ι → Matrix m m ℂ} (h : ∀ j, Commute Z (A j)) (T : Transport.MeanTree ι) :
    Commute Z (T.eval A) := by
  induction T with
  | leaf j => exact h j
  | node p l r ihl ihr =>
    rw [Transport.MeanTree.eval_node, Matrix.geomMean]
    have ha := commute_rpow_of_commute ihl
    exact ((ha _).mul_right (commute_rpow_of_commute (((ha _).mul_right ihr).mul_right
      (ha _)) _)).mul_right (ha _)

section Bands

variable {K : ℕ} {St : Type v} (Γ : Statuses σ K St X)

theorem XC_subset_P (s : St) (g : Fin K) : XC X ⊆ Γ.P s g :=
  Finset.insert_subset_insert _ (Finset.map_subset_map.2 Finset.subset_union_left)

omit [Fintype σ] in
theorem disjoint_physReg_XC {Q : Finset σ} (h : Disjoint X Q) : Disjoint (physReg Q) (XC X) :=
  Finset.disjoint_insert_right.2 ⟨by simp [physReg], (Finset.disjoint_map _).2 h.symm⟩

theorem disjoint_F_XC (s : St) (g : Fin K) : Disjoint (Γ.F s g) (XC X) :=
  Finset.disjoint_insert_left.2 ⟨R_not_mem_XC, disjoint_physReg_XC (Γ.disjoint_XV s g)⟩

theorem commute_pinProj_W [∀ v, NeZero (n v)] (E : TypicalSet D X) {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    {Q : Finset (Site σ)} (hQ : XC X ⊆ Q ∨ Disjoint Q (XC X)) :
    Commute (pinProj E k) (Replicas.W (fun f => Fin (dims n E.d f)) t k Q) ∧
      Commute (pinProj E k) (Replicas.W (fun f => Fin (dims n E.d f)) t k Q)⁻¹ :=
  ⟨commute_pinProj_labelObservable E hQ _, by
    rw [Replicas.W_inv _ ht]; exact commute_pinProj_labelObservable E hQ _⟩

theorem commute_pinProj_Pi (E : TypicalSet D X) (k : ℕ) :
    Commute (pinProj E k) (Transport.Pi (dims n E.d) k) :=
  (Transport.commute_Pi_of_forall fun π => by
    rw [← TensorPower.subsystemPerm_univ]
    exact commute_permOp_of_invariant _ π
      (pinProj_copyPerm E (Or.inl (Finset.subset_univ _)) π)).symm

end Bands

/-- D8.15 (`comparator:pin-norm`).
`N² ≥ (z/d_*²)^k ‖𝓜^{-s} π^λ_R post_k‖²`. -/
theorem step_8_15 : Step_8_15.{u, v} := by
  intro σ _ _ n _ D X E K St _ _ Γ T a ha k l
  have hz := z_pos E
  -- D8.15.1: `𝖯` commutes with every `A_{j,g}` (`XC ⊆ P_{j,g}`; `F_{j,g}`, `Y_{j,g}` disjoint
  -- from `XC`)
  have h1 : ∀ s g, Commute (pinProj E k) (Γ.bandA n E.d (a / 2) k s g) := fun s g => by
    have ht : (0 : ℝ) ≤ a / 2 := by linarith
    have hP := commute_pinProj_W E ht (k := k) (Or.inl (XC_subset_P Γ s g))
    have hF := commute_pinProj_W E ht (k := k) (Or.inr (disjoint_F_XC Γ s g))
    have hY := commute_pinProj_W E ht (k := k)
      (Or.inr (disjoint_physReg_XC (Γ.disjoint_XY s g)))
    have hPi := commute_pinProj_Pi E k
    unfold Statuses.bandA Transport.bandMetric Replicas.A
    exact (hPi.mul_right (((hP.2.mul_right hF.2).mul_right hY.1).pow_right 2)).add_right
      ((Commute.one_right _).sub_right hPi)
  -- D8.15.2: `𝖯` commutes with each `A_j`, with `𝓜` and with `𝓜^{-s}`
  have h2 : Commute (pinProj E k) (Γ.root n E.d T (a / 2) k ^ (-(1 / 4) : ℝ)) :=
    commute_rpow_of_commute (commute_eval_of_commute (fun s => Commute.list_prod_right _ _
      fun b hb => by
        obtain ⟨g, rfl⟩ := List.mem_ofFn.1 hb
        exact h1 s g) T) _
  -- D8.15.3: `N ≥ ‖𝖯 𝓜^{-s} pre_k‖ = ‖𝓜^{-s} 𝖯 pre_k‖`, and D8.14
  have h3 : pinProj E k *ᵥ Matrix.Transport.filteredRaw (Γ.root n E.d T (a / 2) k)
      (pre D E.d k l) = (((Real.sqrt E.z / E.d) ^ k : ℝ) : ℂ) •
        Matrix.Transport.filteredRaw (Γ.root n E.d T (a / 2) k) (piR E.d k l *ᵥ post E k) := by
    rw [Matrix.Transport.filteredRaw, Matrix.Transport.filteredRaw, mulVec_mulVec, h2.eq,
      ← mulVec_mulVec, step_8_14, mulVec_smul]
    push_cast
    rfl
  have h4 := re_star_mulVec_le (isHermitian_pinProj E k) (pinProj_mul_self E k)
    (Matrix.Transport.filteredRaw (Γ.root n E.d T (a / 2) k) (pre D E.d k l))
  rw [h3] at h4
  simp only [star_smul, smul_dotProduct, dotProduct_smul, Complex.star_def,
    Complex.conj_ofReal, smul_eq_mul, Complex.re_ofReal_mul] at h4
  rw [N2, Matrix.Transport.filteredNormSq, Matrix.Transport.filteredNormSq]
  convert h4 using 1
  rw [← mul_assoc, ← mul_pow, div_mul_div_comm, Real.mul_self_sqrt hz.le, sq]

/-! ## D8.16 Pinned metric -/

section Pinned

omit [Fintype σ] [DecidableEq σ] in
theorem permOp_fixFactor_of_disjoint {I : Type*} [DecidableEq I] [Fintype I] {ι : I → Type*}
    [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)] {k : ℕ} {B Q : Finset I} (hBQ : Disjoint B Q)
    (φ : ((f : B) → ι f) → ℂ) (z : Replicas.Config ι k → ℂ) (π : Equiv.Perm (Fin k)) :
    permOp (Replicas.copyPerm ι k Q) π *ᵥ Replicas.fixFactor ι k B φ z =
      Replicas.fixFactor ι k B φ (permOp (Replicas.copyPerm ι k Q) π *ᵥ z) := by
  rw [permOp_mulVec, permOp_mulVec, ← map_inv]
  funext x
  simp only [Replicas.fixFactor, Function.comp_apply]
  congr 1
  refine Finset.prod_congr rfl fun j _ => congrArg φ (funext fun f => ?_)
  simp only [Replicas.copyPerm_apply, if_neg (Finset.disjoint_left.1 hBQ f.2)]

omit [Fintype σ] [DecidableEq σ] in
/-- The fixed-factor identity for a region `Q` disjoint from `B`:
`G_Q (φ^{⊗k} ⊗ z) = φ^{⊗k} ⊗ G_Q z` for every central label function `G`. -/
theorem labelObservable_fixFactor_of_disjoint {I : Type*} [DecidableEq I] [Fintype I]
    {ι : I → Type*} [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)] {k : ℕ} {B Q : Finset I}
    (hBQ : Disjoint B Q) (φ : ((f : B) → ι f) → ℂ) (z : Replicas.Config ι k → ℂ)
    (g : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) :
    labelObservable (Replicas.copyPerm ι k Q) g *ᵥ Replicas.fixFactor ι k B φ z =
      Replicas.fixFactor ι k B φ (labelObservable (Replicas.copyPerm ι k Q) g *ᵥ z) := by
  simp only [labelObservable, labelProj, groupAlgebraRep_eq_sum, sum_mulVec, smul_mulVec,
    permOp_fixFactor_of_disjoint hBQ]
  funext x
  simp [Replicas.fixFactor, Finset.sum_apply, Finset.mul_sum, mul_left_comm]

omit [Fintype σ] [DecidableEq σ] in
/-- On `𝒮_k` a central label function of `Q` equals that of `Q^c` (Lemma 6.1 (2)). -/
theorem labelObservable_mulVec_compl {I : Type*} [DecidableEq I] [Fintype I] {ι : I → Type*}
    [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)] {k : ℕ} (Q : Finset I)
    (g : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) {z : Replicas.Config ι k → ℂ}
    (hz : z ∈ Replicas.S ι k) :
    labelObservable (Replicas.copyPerm ι k Q) g *ᵥ z =
      labelObservable (Replicas.copyPerm ι k Qᶜ) g *ᵥ z := by
  have h := fun l => Replicas.step_6_4_9 ι k Q l hz
  simp only [Replicas.π] at h
  simp only [labelObservable, sum_mulVec, smul_mulVec, h]

omit [Fintype σ] [DecidableEq σ] in
/-- D6.9 (`replicas:leaf-floor`), log formula, for three regions whose labels commute pairwise
(nested or disjoint, Lemma 6.1 (2)): `‖log A_k - a (F_P + F_F - F_Y)‖ ≤ C log(k + 2)`. -/
theorem log_A_of_commute {I : Type*} [DecidableEq I] [Fintype I] (ι : I → Type*)
    [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)] [∀ f, Nonempty (ι f)] {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (P Y F : Finset I),
      (∀ α β : IrrepLabel (Equiv.Perm (Fin k)),
        Commute (labelProj (TensorPower.subsystemPerm k ι P) α)
          (labelProj (TensorPower.subsystemPerm k ι F) β)) →
      (∀ α γ : IrrepLabel (Equiv.Perm (Fin k)),
        Commute (labelProj (TensorPower.subsystemPerm k ι P) α)
          (labelProj (TensorPower.subsystemPerm k ι Y) γ)) →
      (∀ β γ : IrrepLabel (Equiv.Perm (Fin k)),
        Commute (labelProj (TensorPower.subsystemPerm k ι F) β)
          (labelProj (TensorPower.subsystemPerm k ι Y) γ)) →
      ‖cfc Real.log (Replicas.A ι t k P Y F) -
          ((2 * t : ℝ) : ℂ) • (Replicas.F ι k P + Replicas.F ι k F - Replicas.F ι k Y)‖ ≤
        C * Real.log ((k : ℝ) + 2) := by
  obtain ⟨C₀, hC₀, hweight⟩ := TensorPower.exists_abs_log_replicaLabelWeight_add_le ι ht
  refine ⟨6 * C₀, by positivity, fun k P Y F cPF cPY cFY => ?_⟩
  -- D6.9.1: the joint resolution of the three commuting label decompositions
  let hP := isOrthogonalResolution_labelProj (TensorPower.subsystemPerm k ι P)
  let hF := isOrthogonalResolution_labelProj (TensorPower.subsystemPerm k ι F)
  let hY := isOrthogonalResolution_labelProj (TensorPower.subsystemPerm k ι Y)
  let hPF := hP.prod hF cPF
  let R := hPF.prod hY (fun ab γ =>
    (cPY ab.1 γ).mul_left (cFY ab.2 γ))
  have hRP (f : IrrepLabel (Equiv.Perm (Fin k)) → ℂ) :
      R.hom (fun p => f p.1.1) = hP.hom f :=
    (hPF.prod_hom_fst hY R _).trans (hP.prod_hom_fst hF hPF f)
  have hRF (f : IrrepLabel (Equiv.Perm (Fin k)) → ℂ) :
      R.hom (fun p => f p.1.2) = hF.hom f :=
    (hPF.prod_hom_fst hY R _).trans (hP.prod_hom_snd hF hPF f)
  have hRY (f : IrrepLabel (Equiv.Perm (Fin k)) → ℂ) :
      R.hom (fun p => f p.2) = hY.hom f :=
    hPF.prod_hom_snd hY R f
  have hw (l : IrrepLabel (Equiv.Perm (Fin k))) : 0 < Replicas.w ι t l :=
    TensorPower.replicaLabelWeight_pos ι ht.le l
  have hWP : (Replicas.W ι t k P)⁻¹ =
      R.hom (fun p => (((Replicas.w ι t p.1.1)⁻¹ : ℝ) : ℂ)) := by
    rw [Replicas.W_inv ι ht.le]
    simpa only [labelObservable_eq_hom] using
      (hRP (fun l => (((Replicas.w ι t l)⁻¹ : ℝ) : ℂ))).symm
  have hWF : (Replicas.W ι t k F)⁻¹ =
      R.hom (fun p => (((Replicas.w ι t p.1.2)⁻¹ : ℝ) : ℂ)) := by
    rw [Replicas.W_inv ι ht.le]
    simpa only [labelObservable_eq_hom] using
      (hRF (fun l => (((Replicas.w ι t l)⁻¹ : ℝ) : ℂ))).symm
  have hWY : Replicas.W ι t k Y = R.hom (fun p => (Replicas.w ι t p.2 : ℂ)) := by
    simpa only [Replicas.W, TensorPower.replicaMetric, labelObservable_eq_hom] using
      (hRY (fun l => (Replicas.w ι t l : ℂ))).symm
  let q : (IrrepLabel (Equiv.Perm (Fin k)) × IrrepLabel (Equiv.Perm (Fin k))) ×
      IrrepLabel (Equiv.Perm (Fin k)) → ℝ :=
    fun p => ((Replicas.w ι t p.1.1)⁻¹ * (Replicas.w ι t p.1.2)⁻¹ * Replicas.w ι t p.2) ^ 2
  have hA : Replicas.A ι t k P Y F = R.hom (fun p => (q p : ℂ)) := by
    rw [Replicas.A, hWP, hWF, hWY, ← map_mul, ← map_mul, ← map_pow]
    congr 1
    ext p
    simp only [q, Pi.mul_apply, Pi.pow_apply]
    push_cast
    rfl
  let g : (IrrepLabel (Equiv.Perm (Fin k)) × IrrepLabel (Equiv.Perm (Fin k))) ×
      IrrepLabel (Equiv.Perm (Fin k)) → ℝ :=
    fun p => Real.log p.1.1.dim + Real.log p.1.2.dim - Real.log p.2.dim
  have hG : Replicas.F ι k P + Replicas.F ι k F - Replicas.F ι k Y =
      R.hom (fun p => (g p : ℂ)) := by
    change labelEntropy (TensorPower.subsystemPerm k ι P) +
      labelEntropy (TensorPower.subsystemPerm k ι F) -
        labelEntropy (TensorPower.subsystemPerm k ι Y) = _
    simp only [labelEntropy, labelObservable_eq_hom]
    rw [← hRP, ← hRF, ← hRY, ← map_add, ← map_sub]
    congr 1
    ext p
    simp only [g, Pi.add_apply, Pi.sub_apply, Complex.ofReal_sub, Complex.ofReal_add]
  have hHerm (p : (IrrepLabel (Equiv.Perm (Fin k)) ×
      IrrepLabel (Equiv.Perm (Fin k))) × IrrepLabel (Equiv.Perm (Fin k))) :
      (labelProj (TensorPower.subsystemPerm k ι P) p.1.1 *
        labelProj (TensorPower.subsystemPerm k ι F) p.1.2 *
          labelProj (TensorPower.subsystemPerm k ι Y) p.2).IsHermitian :=
    ((((isHermitian_labelProj _ p.1.1).commute_iff (isHermitian_labelProj _ p.1.2)).mp
      (cPF p.1.1 p.1.2)).commute_iff
        (isHermitian_labelProj _ p.2)).mp
          ((cPY p.1.1 p.2).mul_left (cFY p.1.2 p.2))
  rw [hA, R.cfc_hom hHerm, hG, ← map_smul, ← map_sub]
  have hL : 0 ≤ Real.log ((k : ℝ) + 2) := Real.log_nonneg (by linarith [k.cast_nonneg (α := ℝ)])
  refine R.l2_opNorm_hom_le hHerm (by positivity) fun p hp => ?_
  have hPn : labelProj (TensorPower.subsystemPerm k ι P) p.1.1 ≠ 0 := fun hz =>
    hp (by simp only [hz, zero_mul])
  have hFn : labelProj (TensorPower.subsystemPerm k ι F) p.1.2 ≠ 0 := fun hz =>
    hp (by simp only [hz, mul_zero, zero_mul])
  have hYn : labelProj (TensorPower.subsystemPerm k ι Y) p.2 ≠ 0 := fun hz =>
    hp (by simp only [hz, mul_zero])
  have heP := abs_le.mp (hweight k P p.1.1 hPn)
  have heF := abs_le.mp (hweight k F p.1.2 hFn)
  have heY := abs_le.mp (hweight k Y p.2 hYn)
  -- D6.9.1: `log w_k(λ) = -t log d_λ + O(log(k + 2))` on each of the three labels
  have hlog : Real.log (q p) = 2 * (Real.log (Replicas.w ι t p.2) -
      Real.log (Replicas.w ι t p.1.1) - Real.log (Replicas.w ι t p.1.2)) := by
    simp only [q, Real.log_pow, Real.log_mul (mul_pos (inv_pos.mpr (hw _))
      (inv_pos.mpr (hw _))).ne' (hw _).ne', Real.log_mul (inv_pos.mpr (hw _)).ne'
      (inv_pos.mpr (hw _)).ne', Real.log_inv]
    push_cast
    ring
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, hlog,
    abs_le]
  simp only [g, Replicas.w] at heP heF heY ⊢
  constructor <;> nlinarith

variable [∀ v, NeZero (n v)]

/-- `B_{XC}` as a function of the `XC`-part of a configuration. -/
noncomputable def βXC (E : TypicalSet D X) : ((f : XC X) → Fin (dims n E.d f)) → ℂ :=
  fun y => BXC E fun f => if h : f ∈ XC X then y ⟨f, h⟩ else 0

theorem βXC_apply (E : TypicalSet D X) (x : SiteConfig (dims n E.d)) :
    βXC E (fun f => x f) = BXC E x :=
  BXC_congr E fun f hf => by simp [hf]

/-- The `(XC)^c`-part `⟨B_{XC}^{⊗k}|_{XC} ψ` of `𝖯 ψ`. -/
noncomputable def zPin (E : TypicalSet D X) (k : ℕ) (ψ : Transport.Config (dims n E.d) k → ℂ) :
    Transport.Config (dims n E.d) k → ℂ :=
  fun x => ∑ y, (∏ j, star (BXC E (y j))) *
    (if ∀ j, ∀ f ∉ XC X, x j f = y j f then 1 else 0) * ψ y

omit [∀ v, NeZero (n v)] in
theorem zPin_congr (E : TypicalSet D X) (k : ℕ) (ψ : Transport.Config (dims n E.d) k → ℂ)
    (x x' : Transport.Config (dims n E.d) k) (h : ∀ j, ∀ f, f ∉ XC X → x j f = x' j f) :
    zPin E k ψ x = zPin E k ψ x' := by
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hx : ∀ j, ∀ f ∉ XC X, x j f = y j f
  · have hx' : ∀ j, ∀ f ∉ XC X, x' j f = y j f := fun j f hf => (h j f hf).symm.trans (hx j f hf)
    simp only [if_pos hx, if_pos hx']
  · have hx' : ¬ ∀ j, ∀ f ∉ XC X, x' j f = y j f := fun hx' =>
      hx fun j f hf => (h j f hf).trans (hx' j f hf)
    simp only [if_neg hx, if_neg hx']

/-- `𝖯 ψ = B_{XC}^{⊗k} ⊗ ⟨B_{XC}^{⊗k}| ψ`. -/
theorem pinProj_mulVec (E : TypicalSet D X) (k : ℕ)
    (ψ : Transport.Config (dims n E.d) k → ℂ) :
    pinProj E k *ᵥ ψ =
      Replicas.fixFactor (fun f => Fin (dims n E.d f)) k (XC X) (βXC E) (zPin E k ψ) := by
  funext x
  simp only [mulVec, dotProduct, pinProj, Replicas.fixFactor, zPin, βXC_apply, Finset.mul_sum,
    Finset.prod_mul_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- On `ran 𝖯`, a central label function of `C X Q` (`Q` physical, disjoint from `X`) acts as the
one of `Q` (fixed-factor identity, fixed vector `B_{XC}^{⊗k}`). -/
theorem labelObservable_pinned (E : TypicalSet D X) {k : ℕ} {Q : Finset σ} (hXQ : Disjoint X Q)
    (g : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) {ψ : Transport.Config (dims n E.d) k → ℂ}
    (hψ : pinProj E k *ᵥ ψ = ψ) :
    labelObservable (Replicas.copyPerm (fun f => Fin (dims n E.d f)) k
        (insert .C (physReg (X ∪ Q)))) g *ᵥ ψ =
      labelObservable (Replicas.copyPerm (fun f => Fin (dims n E.d f)) k (physReg Q)) g *ᵥ ψ := by
  have hd := (disjoint_physReg_XC hXQ).symm
  have e : insert Site.C (physReg (X ∪ Q)) = XC X ∪ physReg Q := by
    rw [XC, Finset.insert_union, physReg, physReg, physReg, Finset.map_union]
  rw [← hψ, pinProj_mulVec, e,
    Replicas.eq_replicas_fixed_factor _ k hd _ (zPin_congr E k ψ) g,
    labelObservable_fixFactor_of_disjoint hd]

omit [∀ v, NeZero (n v)] in
/-- A central label function of a physical region disjoint from `X` preserves the pinned
symmetric range `𝒮_k ∩ ran 𝖯`. -/
theorem pinned_labelObservable (E : TypicalSet D X) {k : ℕ} {Q : Finset σ} (hXQ : Disjoint X Q)
    (g : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) {ψ : Transport.Config (dims n E.d) k → ℂ}
    (hψ : ψ ∈ Replicas.S (fun f => Fin (dims n E.d f)) k ∧ pinProj E k *ᵥ ψ = ψ) :
    labelObservable (Replicas.copyPerm (fun f => Fin (dims n E.d f)) k (physReg Q)) g *ᵥ ψ ∈
        Replicas.S (fun f => Fin (dims n E.d f)) k ∧
      pinProj E k *ᵥ (labelObservable (Replicas.copyPerm (fun f => Fin (dims n E.d f)) k
        (physReg Q)) g *ᵥ ψ) =
        labelObservable (Replicas.copyPerm (fun f => Fin (dims n E.d f)) k (physReg Q)) g *ᵥ ψ := by
  refine ⟨fun π => ?_, ?_⟩
  · have hS : ∀ π, permOp (Replicas.copyPerm (fun f => Fin (dims n E.d f)) k Finset.univ) π *ᵥ
        ψ = ψ := hψ.1
    have hc : Commute (permOp (Replicas.copyPerm (fun f => Fin (dims n E.d f)) k Finset.univ) π)
        (labelObservable (Replicas.copyPerm (fun f => Fin (dims n E.d f)) k (physReg Q)) g) := by
      change Commute (permOp (TensorPower.subsystemPerm k _ Finset.univ) π) _
      rw [TensorPower.subsystemPerm_univ]
      exact TensorPower.commute_copyPerm_labelObservable k (physReg Q) g π
    change permOp (Replicas.copyPerm (fun f => Fin (dims n E.d f)) k Finset.univ) π *ᵥ _ = _
    rw [mulVec_mulVec, hc.eq, ← mulVec_mulVec, hS π]
  · rw [mulVec_mulVec, (commute_pinProj_labelObservable E
      (Or.inr (disjoint_physReg_XC hXQ)) g).eq, ← mulVec_mulVec, hψ.2]

omit [∀ v, NeZero (n v)] in
theorem compl_F {K : ℕ} {St : Type v} (Γ : Statuses σ K St X) (s : St) (g : Fin K) :
    (Γ.F s g)ᶜ = insert Site.C (physReg (X ∪ (Γ.U s g ∪ Γ.Y s g))) := by
  ext f
  cases f with
  | phys v =>
    simp only [Finset.mem_compl, Statuses.F, Finset.mem_insert, reduceCtorEq, false_or,
      mem_physReg, Finset.mem_union]
    have hc : v ∈ X ∪ Γ.U s g ∪ Γ.Y s g ∪ Γ.V s g := by
      rw [Γ.cover s g]; exact Finset.mem_univ v
    simp only [Finset.mem_union] at hc
    have h1 : v ∈ X → v ∉ Γ.V s g := fun h => Finset.disjoint_left.1 (Γ.disjoint_XV s g) h
    have h2 : v ∈ Γ.U s g → v ∉ Γ.V s g := fun h => Finset.disjoint_left.1 (Γ.disjoint_UV s g) h
    have h3 : v ∈ Γ.Y s g → v ∉ Γ.V s g := fun h => Finset.disjoint_left.1 (Γ.disjoint_YV s g) h
    tauto
  | C => simp [Statuses.F, physReg]
  | R => simp [Statuses.F, physReg]

omit [Fintype σ] [DecidableEq σ] [∀ v, NeZero (n v)] in
/-- If `M_i = N_i` on a set preserved by the `N_i`, then `(M₁M₂M₃)²` and `(N₁N₂N₃)²` agree on
it, and the image stays in the set. -/
theorem sq_mulVec_eq {m : Type*} [Fintype m] [DecidableEq m] {M₁ M₂ M₃ N₁ N₂ N₃ : Matrix m m ℂ}
    (Kp : (m → ℂ) → Prop) (h₁ : ∀ ψ, Kp ψ → M₁ *ᵥ ψ = N₁ *ᵥ ψ)
    (h₂ : ∀ ψ, Kp ψ → M₂ *ᵥ ψ = N₂ *ᵥ ψ) (h₃ : ∀ ψ, Kp ψ → M₃ *ᵥ ψ = N₃ *ᵥ ψ)
    (k₁ : ∀ ψ, Kp ψ → Kp (N₁ *ᵥ ψ)) (k₂ : ∀ ψ, Kp ψ → Kp (N₂ *ᵥ ψ))
    (k₃ : ∀ ψ, Kp ψ → Kp (N₃ *ᵥ ψ)) {φ : m → ℂ} (hφ : Kp φ) :
    (M₁ * M₂ * M₃) ^ 2 *ᵥ φ = (N₁ * N₂ * N₃) ^ 2 *ᵥ φ ∧ Kp ((N₁ * N₂ * N₃) ^ 2 *ᵥ φ) := by
  have step : ∀ ψ, Kp ψ → (M₁ * M₂ * M₃) *ᵥ ψ = (N₁ * N₂ * N₃) *ᵥ ψ ∧
      Kp ((N₁ * N₂ * N₃) *ᵥ ψ) := fun ψ hψ => by
    simp only [← mulVec_mulVec]
    rw [h₃ ψ hψ, h₂ _ (k₃ ψ hψ), h₁ _ (k₂ _ (k₃ ψ hψ))]
    exact ⟨rfl, k₁ _ (k₂ _ (k₃ ψ hψ))⟩
  obtain ⟨e1, k1⟩ := step φ hφ
  obtain ⟨e2, k2⟩ := step _ k1
  rw [sq, sq, ← mulVec_mulVec φ (M₁ * M₂ * M₃), ← mulVec_mulVec φ (N₁ * N₂ * N₃), e1, e2]
  exact ⟨rfl, k2⟩

omit [∀ v, NeZero (n v)] in
/-- D8.1, Output (iii): within one leaf the regions `U_g, U_gY_g, Y_g` of any two bands are
nested or disjoint. -/
theorem band_rel {K : ℕ} {St : Type v} (Γ : Statuses σ K St X) (s : St) (g g' : Fin K)
    {R R' : Finset σ} (hR : R = Γ.U s g ∨ R = Γ.U s g ∪ Γ.Y s g ∨ R = Γ.Y s g)
    (hR' : R' = Γ.U s g' ∨ R' = Γ.U s g' ∪ Γ.Y s g' ∨ R' = Γ.Y s g') :
    R ⊆ R' ∨ R' ⊆ R ∨ Disjoint R R' := by
  have hsub : ∀ {g g' : Fin K}, g < g' → Γ.U s g ∪ Γ.Y s g ⊆ Γ.U s g' := fun {g g'} h x hx => by
    have hX : x ∉ X := by
      rcases Finset.mem_union.1 hx with h | h
      · exact Finset.disjoint_right.1 (Γ.disjoint_XU s g) h
      · exact Finset.disjoint_right.1 (Γ.disjoint_XY s g) h
    have := Γ.nesting s s g g' h (show x ∈ X ∪ Γ.U s g ∪ Γ.Y s g by
      rcases Finset.mem_union.1 hx with h | h <;> simp [Finset.mem_union, h])
    rcases Finset.mem_union.1 this with h | h
    · exact absurd h hX
    · exact h
  have hsub' : ∀ {g : Fin K} {R : Finset σ},
      (R = Γ.U s g ∨ R = Γ.U s g ∪ Γ.Y s g ∨ R = Γ.Y s g) → R ⊆ Γ.U s g ∪ Γ.Y s g := by
    rintro g R (rfl | rfl | rfl)
    · exact Finset.subset_union_left
    · exact Finset.Subset.rfl
    · exact Finset.subset_union_right
  rcases lt_trichotomy g g' with h | rfl | h
  · have hRU := (hsub' hR).trans (hsub h)
    rcases hR' with rfl | rfl | rfl
    · exact Or.inl hRU
    · exact Or.inl (hRU.trans Finset.subset_union_left)
    · exact Or.inr (Or.inr (Finset.disjoint_of_subset_left hRU (Γ.disjoint_UY s g')))
  · rcases hR with rfl | rfl | rfl <;> rcases hR' with rfl | rfl | rfl <;>
    first
    | exact Or.inl Finset.Subset.rfl
    | exact Or.inl Finset.subset_union_left
    | exact Or.inl Finset.subset_union_right
    | exact Or.inr (Or.inl Finset.subset_union_left)
    | exact Or.inr (Or.inl Finset.subset_union_right)
    | exact Or.inr (Or.inr (Γ.disjoint_UY s g))
    | exact Or.inr (Or.inr (Γ.disjoint_UY s g).symm)
  · have hRU := (hsub' hR').trans (hsub h)
    rcases hR with rfl | rfl | rfl
    · exact Or.inr (Or.inl hRU)
    · exact Or.inr (Or.inl (hRU.trans Finset.subset_union_left))
    · exact Or.inr (Or.inr (Finset.disjoint_of_subset_right hRU (Γ.disjoint_UY s g).symm))

omit [∀ v, NeZero (n v)] in
theorem commute_labelObservable_physReg {d k : ℕ} {Q Q' : Finset σ}
    (h : Q ⊆ Q' ∨ Q' ⊆ Q ∨ Disjoint Q Q') (f f' : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) :
    Commute (labelObservable (Replicas.copyPerm (fun x => Fin (dims n d x)) k (physReg Q)) f)
      (labelObservable (Replicas.copyPerm (fun x => Fin (dims n d x)) k (physReg Q')) f') := by
  rcases h with h | h | h
  · exact Replicas.commute_labelObservable _ k (Or.inl (Finset.map_subset_map.2 h)) f f'
  · exact (Replicas.commute_labelObservable _ k (Or.inl (Finset.map_subset_map.2 h)) f' f).symm
  · exact Replicas.commute_labelObservable _ k (Or.inr ((Finset.disjoint_map _).2 h)) f f'

/-- D8.16 (`comparator:pinned-metric`). On the pinned symmetric range
(`B_{XC}^{⊗k} ⊗` symmetric vector on the rest), `P_{j,g}`-label = `U_{j,g}`-label,
`F_{j,g}`-label = `U_{j,g}Y_{j,g}`-label, and `A_{j,g}` restricts exactly to
`Ã_{j,g} = (W_{U_{j,g}}^{-1} W_{U_{j,g}Y_{j,g}}^{-1} W_{Y_{j,g}})²`,
`log Ã_{j,g} = a (F_{U_{j,g}} + F_{U_{j,g}Y_{j,g}} - F_{Y_{j,g}}) + O(log(k + 1)) id`.
Error is an operator-norm bound, not asserted scalar. -/
theorem step_8_16 : Step_8_16.{u, v} := by
  intro σ _ _ n _ D X E K St Γ
  refine ⟨fun t ht k s g => ?_, fun t ht _ => ?_⟩
  · have hWinv : ∀ Q, (Replicas.W (fun f => Fin (dims n E.d f)) t k Q)⁻¹ =
        labelObservable (Replicas.copyPerm (fun f => Fin (dims n E.d f)) k Q)
          fun l => (Replicas.w (fun f => Fin (dims n E.d f)) t l)⁻¹ :=
      fun Q => Replicas.W_inv _ ht k Q
    have hW : ∀ Q, Replicas.W (fun f => Fin (dims n E.d f)) t k Q =
        labelObservable (Replicas.copyPerm (fun f => Fin (dims n E.d f)) k Q)
          fun l => Replicas.w (fun f => Fin (dims n E.d f)) t l := fun Q => rfl
    have hXUY : Disjoint X (Γ.U s g ∪ Γ.Y s g) :=
      Finset.disjoint_union_right.2 ⟨Γ.disjoint_XU s g, Γ.disjoint_XY s g⟩
    refine ⟨fun φ hφS hφP => ?_, ?_, fun g' => ?_⟩
    · obtain ⟨hA, hK⟩ := sq_mulVec_eq
        (M₁ := (Replicas.W (fun f => Fin (dims n E.d f)) t k (Γ.P s g))⁻¹)
        (M₂ := (Replicas.W (fun f => Fin (dims n E.d f)) t k (Γ.F s g))⁻¹)
        (M₃ := Replicas.W (fun f => Fin (dims n E.d f)) t k (Γ.Yr s g))
        (N₁ := (Replicas.W (fun f => Fin (dims n E.d f)) t k (physReg (Γ.U s g)))⁻¹)
        (N₂ := (Replicas.W (fun f => Fin (dims n E.d f)) t k
          (physReg (Γ.U s g ∪ Γ.Y s g)))⁻¹)
        (N₃ := Replicas.W (fun f => Fin (dims n E.d f)) t k (physReg (Γ.Y s g)))
        (fun ψ => ψ ∈ Replicas.S (fun f => Fin (dims n E.d f)) k ∧ pinProj E k *ᵥ ψ = ψ)
        -- D8.16.1: `W_{CXU} → W_U` by the fixed-factor identity
        (fun ψ hψ => by
          rw [hWinv, hWinv]
          exact labelObservable_pinned E (Γ.disjoint_XU s g) _ hψ.2)
        -- D8.16.2: on `𝒮_k`, `W_{RV} = W_{CXUY} → W_{UY}`; `W_Y` unaffected
        (fun ψ hψ => by
          rw [hWinv, hWinv, labelObservable_mulVec_compl _ _ hψ.1, compl_F]
          exact labelObservable_pinned E hXUY _ hψ.2)
        (fun ψ _ => rfl)
        (fun ψ hψ => by rw [hWinv]; exact pinned_labelObservable E (Γ.disjoint_XU s g) _ hψ)
        (fun ψ hψ => by rw [hWinv]; exact pinned_labelObservable E hXUY _ hψ)
        (fun ψ hψ => by rw [hW]; exact pinned_labelObservable E (Γ.disjoint_XY s g) _ hψ)
        ⟨hφS, hφP⟩
      -- D8.16.4: `𝖯` commutes with `A_{j,g}`, so `Ã φ` stays in the pinned symmetric range
      have hPi : ∀ ψ ∈ Replicas.S (fun f => Fin (dims n E.d f)) k,
          Transport.Pi (dims n E.d) k *ᵥ ψ = ψ := fun ψ hψ =>
        symProj_mulVec_of_mem _ (by rw [← TensorPower.subsystemPerm_univ]; exact hψ)
      refine ⟨?_, hK.1, hK.2⟩
      change (Transport.Pi _ k * Replicas.A _ t k (Γ.P s g) (Γ.Yr s g) (Γ.F s g) +
        (1 - Transport.Pi _ k)) *ᵥ φ = _
      rw [add_mulVec, sub_mulVec, one_mulVec, ← mulVec_mulVec, hPi φ hφS, sub_self, add_zero,
        Replicas.A, hA, hPi _ hK.1]
      rfl
    · have hWpd : ∀ Q, (Replicas.W (fun f => Fin (dims n E.d f)) t k Q).PosDef :=
        fun Q => (Replicas.lemma_6_2_1 _ ht k Q).1
      have c12 := commute_labelObservable_physReg (n := n) (d := E.d) (k := k)
        (Q := Γ.U s g) (Q' := Γ.U s g ∪ Γ.Y s g) (Or.inl Finset.subset_union_left)
        (fun l => (Replicas.w (fun f => Fin (dims n E.d f)) t l)⁻¹)
        (fun l => (Replicas.w (fun f => Fin (dims n E.d f)) t l)⁻¹)
      have c13 := commute_labelObservable_physReg (n := n) (d := E.d) (k := k)
        (Q := Γ.U s g) (Q' := Γ.Y s g) (Or.inr (Or.inr (Γ.disjoint_UY s g)))
        (fun l => (Replicas.w (fun f => Fin (dims n E.d f)) t l)⁻¹)
        (fun l => Replicas.w (fun f => Fin (dims n E.d f)) t l)
      have c23 := commute_labelObservable_physReg (n := n) (d := E.d) (k := k)
        (Q := Γ.U s g ∪ Γ.Y s g) (Q' := Γ.Y s g) (Or.inr (Or.inl Finset.subset_union_right))
        (fun l => (Replicas.w (fun f => Fin (dims n E.d f)) t l)⁻¹)
        (fun l => Replicas.w (fun f => Fin (dims n E.d f)) t l)
      rw [← hWinv, ← hWinv] at c12
      rw [← hWinv, ← hW] at c13 c23
      have hN := (((hWpd _).inv.mul_of_commute (hWpd _).inv c12).mul_of_commute (hWpd _)
        (c13.mul_left c23))
      exact (hN.posSemidef.pow 2).posDef_iff_isUnit.mpr (hN.isUnit.pow 2)
    · simp only [Statuses.Atil, hWinv]
      simp only [hW]
      refine Commute.pow_pow ?_ 2 2
      refine Commute.mul_left (Commute.mul_left ?_ ?_) ?_ <;>
        refine Commute.mul_right (Commute.mul_right ?_ ?_) ?_ <;>
        exact commute_labelObservable_physReg (band_rel Γ s g g' (by simp) (by simp)) _ _
  · -- D8.16.3: the log formula of `replicas:leaf-floor` for the regions `U, Y, UY`
    obtain ⟨C, -, hC⟩ := log_A_of_commute (fun f => Fin (dims n E.d f)) ht
    exact ⟨C, fun k s g => hC k _ _ _
      (fun α β => Replicas.step_6_4_8 _ k (Or.inl (Finset.map_subset_map.2
        Finset.subset_union_left)) α β)
      (fun α γ => Replicas.step_6_4_8 _ k (Or.inr ((Finset.disjoint_map _).2
        (Γ.disjoint_UY s g))) α γ)
      (fun β γ => (Replicas.step_6_4_8 _ k (Or.inl (Finset.map_subset_map.2
        Finset.subset_union_right)) γ β).symm)⟩

end Pinned

end AreaLaw.Comparators
