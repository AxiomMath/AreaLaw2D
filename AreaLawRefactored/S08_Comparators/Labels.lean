import AreaLawRefactored.S08_Comparators.Interfaces
import AreaLawForMathlib.Algebra.BigOperators.IidSecondMoment

/-!
# §8.2 Labels selected by the auxiliary pair (D8.9–D8.13)

Digest `digest/08-comparators.md` D8.9–D8.13, paper `paper/sections/07-comparators.tex` 218–281.
No geometry. D8.9 (`comparator:label-remainder`) is Lemma 6.1 (5) (`Replicas.lemma_6_1_5`); on
`k` copies of a fixed finite system `Ω` (basis `Fin k → Ω`, copy permutations
`TensorPower.copyPerm Ω k`) it is `TensorPower.schurSurprisal`, and its eigenvalue repetition
`u d_λ ≤ 1` is `mul_dim_le_one_of_ne_zero`. Every expectation `Tr ρ f(ρ, F)` of a
permutation-invariant density `ρ` is a sum over the joint resolution `E_u π^λ` of `ρ` and the
labels (`isOrthogonalResolution_joint`), with masses `Tr E_u π^λ ≥ 0`.

The label probabilities of a product vector `φ^{⊗k}` on `k` copies of `𝒱` are those of the iid
`R`-marginal of `φ` (`star_piR_dotProduct_piR_tensorVec`): `q_k` is the label law of
`diag(p'_i)^{⊗k}` (D8.12.1) and `‖pre_k‖²` that of the maximally mixed `R`-marginal of `Bell`
(D8.13.1).
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix Filter Topology Arealaw Entropy PermutationRepresentation TensorPower

namespace AreaLaw.Comparators

universe u v

/-! ## The joint resolution of a permutation-invariant density -/

section Joint

variable {G X : Type*} [Group G] [Fintype G] [Fintype X] [DecidableEq X]
  (φ : G →* Equiv.Perm X) {ρ : Matrix X X ℂ} (hρ : ρ.PosSemidef)

/-- The mass `Tr E_u π^λ` of the joint projection of the eigenvalue `u` of `ρ` and the label
`λ`. -/
noncomputable def jointMass (p : hρ.isHermitian.eigenvalueSet × IrrepLabel G) : ℝ :=
  (hρ.isHermitian.spectralProj p.1 * labelProj φ p.2).trace.re

omit [Fintype X] [DecidableEq X] in
/-- `π^λ` is the label observable of the indicator of `λ`. -/
theorem labelProj_eq_labelObservable [Fintype X] [DecidableEq X] (l : IrrepLabel G) :
    labelProj φ l = labelObservable φ fun l' => if l' = l then 1 else 0 := by
  simp [labelObservable]

variable {φ} (hinv : ∀ g, Commute (permOp φ g) ρ)
include hinv

theorem jointMass_nonneg (p : hρ.isHermitian.eigenvalueSet × IrrepLabel G) :
    0 ≤ jointMass φ hρ p := by
  rw [jointMass, trace_joint hρ hinv]
  simp

theorem re_trace_joint_hom (c : hρ.isHermitian.eigenvalueSet × IrrepLabel G → ℝ) :
    ((isOrthogonalResolution_joint hρ hinv).hom fun p => (c p : ℂ)).trace.re =
      ∑ p, c p * jointMass φ hρ p := by
  rw [IsOrthogonalResolution.trace_hom, Complex.re_sum]
  exact Finset.sum_congr rfl fun p _ => Complex.re_ofReal_mul _ _

theorem eq_joint_hom :
    ρ = (isOrthogonalResolution_joint hρ hinv).hom fun p => ((p.1 : ℝ) : ℂ) := by
  have h := joint_hom_fst hρ hinv id
  rw [Matrix.IsHermitian.cfc_id] at h
  exact h.symm

/-- D8.9 (`F ≤ L` on the support): `u d_λ ≤ 1` on every joint projection of positive mass. -/
theorem log_dim_le_neg_log (htr : ρ.trace = 1)
    (p : hρ.isHermitian.eigenvalueSet × IrrepLabel G) (hp : jointMass φ hρ p ≠ 0)
    (hpos : 0 < (p.1 : ℝ)) : Real.log p.2.dim ≤ -Real.log (p.1 : ℝ) := by
  have hP : hρ.isHermitian.spectralProj p.1 * labelProj φ p.2 ≠ 0 :=
    fun h0 => hp (by simp [jointMass, h0])
  have hd : (0 : ℝ) < p.2.dim := by exact_mod_cast p.2.dim_pos
  have h := Real.log_nonpos (mul_nonneg hpos.le hd.le)
    (mul_dim_le_one_of_ne_zero hρ hinv htr p hP)
  rw [Real.log_mul hpos.ne' hd.ne'] at h
  linarith

theorem mul_joint_hom (c : hρ.isHermitian.eigenvalueSet × IrrepLabel G → ℂ) :
    ρ * (isOrthogonalResolution_joint hρ hinv).hom c =
      (isOrthogonalResolution_joint hρ hinv).hom fun p => ((p.1 : ℝ) : ℂ) * c p := by
  refine (congrArg (· * _) (eq_joint_hom hρ hinv)).trans ?_
  rw [← map_mul]
  rfl

/-- `Tr f(ρ) = ∑_{u,λ} f(u) Tr E_u π^λ`. -/
theorem re_trace_cfc_eq_sum (f : ℝ → ℝ) :
    (cfc f ρ).trace.re = ∑ p, f p.1 * jointMass φ hρ p := by
  rw [hρ.isHermitian.cfc_eq, ← joint_hom_fst hρ hinv, re_trace_joint_hom hρ hinv]

/-- `Tr ρ f(F) = ∑_{u,λ} u f(log d_λ) Tr E_u π^λ`. -/
theorem re_trace_mul_cfc_labelEntropy_eq_sum (f : ℝ → ℝ) :
    (ρ * cfc f (labelEntropy φ)).trace.re =
      ∑ p, (p.1 : ℝ) * f (Real.log p.2.dim) * jointMass φ hρ p := by
  rw [labelEntropy_eq_joint_hom hρ hinv,
    (isOrthogonalResolution_joint hρ hinv).cfc_hom (isHermitian_joint hρ hinv),
    mul_joint_hom hρ hinv, ← re_trace_joint_hom hρ hinv]
  congr 3
  funext p
  simp

/-- `Tr ρ π^λ = ∑_u u Tr E_u π^λ`. -/
theorem re_trace_mul_labelProj_eq_sum (l : IrrepLabel G) :
    (ρ * labelProj φ l).trace.re =
      ∑ p, (p.1 : ℝ) * (if p.2 = l then 1 else 0) * jointMass φ hρ p := by
  rw [labelProj_eq_labelObservable, ← joint_hom_snd hρ hinv, mul_joint_hom hρ hinv,
    ← re_trace_joint_hom hρ hinv]
  congr 3
  funext p
  push_cast
  rfl

/-- `∑_λ g(λ) Tr ρ π^λ = ∑_{u,λ} u g(λ) Tr E_u π^λ`. -/
theorem sum_mul_re_trace_mul_labelProj_eq_sum (g : IrrepLabel G → ℝ) :
    ∑ l, g l * (ρ * labelProj φ l).trace.re =
      ∑ p, (p.1 : ℝ) * jointMass φ hρ p * g p.2 := by
  simp only [re_trace_mul_labelProj_eq_sum hρ hinv, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_eq_single p.2 (fun l _ hl => by simp [Ne.symm hl]) (by simp)]
  simp only [if_true]
  ring

open scoped Matrix.Norms.L2Operator in
/-- `Tr ρ e^{b(L_ρ - F)} = ∑_{u,λ} u e^{b(-log u - log d_λ)} Tr E_u π^λ`. -/
theorem re_trace_mul_exp_eq_sum (b : ℝ) :
    (ρ * NormedSpace.exp ((b : ℂ) • (-CFC.log ρ - labelEntropy φ))).trace.re =
      ∑ p, (p.1 : ℝ) * Real.exp (b * (-Real.log (p.1 : ℝ) - Real.log p.2.dim)) *
        jointMass φ hρ p := by
  rw [neg_log_eq_joint_hom hρ hinv, labelEntropy_eq_joint_hom hρ hinv, ← map_sub, ← map_smul,
    (isOrthogonalResolution_joint hρ hinv).exp_hom, mul_joint_hom hρ hinv,
    ← re_trace_joint_hom hρ hinv]
  congr 3
  funext p
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  push_cast
  rfl

end Joint

/-! ## D8.10 Signed label moments -/

section Moments

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- `Tr ρ^{1-u} = ∑_{p_i > 0} p_i^{1-u}` for `u < 1`. -/
theorem trace_rpow_eq_trPowPos {ρ : Matrix Ω Ω ℂ} (hρ : ρ.PosSemidef) {u : ℝ} (hu : u < 1) :
    (ρ ^ (1 - u)).trace = (trPowPos ρ hρ.isHermitian u : ℂ) := by
  rw [rpow_eq_unitary_conj_diagonal hρ, trace_mul_comm, ← Matrix.mul_assoc,
    Unitary.coe_star_mul_self, Matrix.one_mul, trace_diagonal, trPowPos]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases (hρ.eigenvalues_nonneg i).lt_or_eq with h | h
  · rw [if_pos h]
  · rw [if_neg h.not_lt, ← h, Real.zero_rpow (by linarith)]

theorem trPowPos_pos {ρ : Matrix Ω Ω ℂ} (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) (u : ℝ) :
    0 < trPowPos ρ hρ.isHermitian u := by
  have hsum : ∑ i, hρ.isHermitian.eigenvalues i = 1 := by
    have h := hρ.isHermitian.trace_eq_sum_eigenvalues
    rw [htr] at h
    have h' := congrArg Complex.re h
    simpa using h'.symm
  obtain ⟨i, hi⟩ : ∃ i, 0 < hρ.isHermitian.eigenvalues i := by
    by_contra h
    push Not at h
    linarith [Finset.sum_nonpos fun i (_ : i ∈ Finset.univ) => h i]
  refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ _, by
    rw [if_pos hi]; exact Real.rpow_pos_of_pos hi _⟩
  split_ifs with h
  · exact (Real.rpow_pos_of_pos h _).le
  · exact le_rfl

/-- The `k`-copy moments of an iid density: `∑_{u,λ} u^{1-u'} Tr E_u π^λ = (Tr ρ^{1-u'})^k`. -/
theorem sum_rpow_jointMass_tensorPow {ρ : Matrix Ω Ω ℂ} (hρ : ρ.PosSemidef) (k : ℕ) {u : ℝ}
    (hu : u < 1) :
    ∑ p, ((p.1 : ℝ) ^ (1 - u)) * jointMass (copyPerm Ω k) (posSemidef_tensorPow hρ) p =
      trPowPos ρ hρ.isHermitian u ^ k := by
  have hρk := posSemidef_tensorPow (k := k) hρ
  have hinv : ∀ σ, Commute (permOp (copyPerm Ω k) σ) (tensorPow (k := k) ρ) := fun σ =>
    commute_permOp_copyPerm_tensorPow ρ σ
  have h := re_trace_cfc_eq_sum hρk hinv fun x : ℝ => x ^ (1 - u)
  rw [← h, ← CFC.rpow_eq_cfc_real hρk.nonneg,
    ← tensorPow_rpow hρ (by linarith), trace_tensorPow, trace_rpow_eq_trPowPos hρ hu]
  norm_cast

/-- A positive combination of a probability vector is positive. -/
theorem sum_mul_pos_of_sum_eq_one {ι : Type*} [Fintype ι] {w g : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (hg : ∀ i, 0 < g i) : 0 < ∑ i, w i * g i := by
  obtain ⟨i, hi⟩ : ∃ i, 0 < w i := by
    by_contra h
    push Not at h
    linarith [Finset.sum_nonpos fun i (_ : i ∈ Finset.univ) => h i]
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hw j) (hg j).le)
    ⟨i, Finset.mem_univ _, mul_pos hi (hg i)⟩

/-- `Tr ρ^{⊗k} g(F) = ∑_{u,λ} u g(log d_λ) Tr E_u π^λ` for the joint resolution of `ρ^{⊗k}`. -/
theorem re_trace_tensorPow_mul_cfc {ρ : Matrix Ω Ω ℂ} (hρ : ρ.PosSemidef) (k : ℕ) (g : ℝ → ℝ) :
    (trace (tensorPow (k := k) ρ * cfc g (labelObservable (copyPerm Ω k)
      fun l => Real.log l.dim))).re =
      ∑ p, (p.1 : ℝ) * jointMass (copyPerm Ω k) (posSemidef_tensorPow hρ) p *
        g (Real.log p.2.dim) := by
  rw [← labelEntropy, re_trace_mul_cfc_labelEntropy_eq_sum (posSemidef_tensorPow hρ)
    (commute_permOp_copyPerm_tensorPow ρ)]
  exact Finset.sum_congr rfl fun p _ => by ring

/-- The weights `u Tr E_u π^λ` of the joint resolution of `ρ^{⊗k}` are a probability vector. -/
theorem sum_jointMass_tensorPow {ρ : Matrix Ω Ω ℂ} (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (k : ℕ) : ∑ p, (p.1 : ℝ) * jointMass (copyPerm Ω k) (posSemidef_tensorPow hρ) p = 1 := by
  have h := re_trace_joint_hom (posSemidef_tensorPow (k := k) hρ)
    (commute_permOp_copyPerm_tensorPow ρ) fun p => (p.1 : ℝ)
  rw [← eq_joint_hom (posSemidef_tensorPow hρ) (commute_permOp_copyPerm_tensorPow ρ),
    trace_tensorPow, htr, one_pow] at h
  simpa using h.symm

/-- D8.5 for `ρ^{⊗k}`: `log Tr ρ^{1-v} ≤ vS + C₀𝓑v²` gives
`∑_{u,λ} u^{1-v} Tr E_u π^λ = (Tr ρ^{1-v})^k ≤ e^{k(vS + C₀𝓑v²)}`. -/
theorem sum_rpow_jointMass_tensorPow_le {ρ : Matrix Ω Ω ℂ} (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) (k : ℕ) {v S C : ℝ} (hv : v < 1)
    (hmgf : Real.log (trPowPos ρ hρ.isHermitian v) ≤ v * S + C * v ^ 2) :
    ∑ p, ((p.1 : ℝ) ^ (1 - v)) * jointMass (copyPerm Ω k) (posSemidef_tensorPow hρ) p ≤
      Real.exp (k * (v * S + C * v ^ 2)) := by
  rw [sum_rpow_jointMass_tensorPow hρ k hv, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (trPowPos_pos hρ htr v).le
    ((Real.log_le_iff_le_exp (trPowPos_pos hρ htr v)).mp hmgf) k

/-- D8.10.1. `+` sign: `F ≤ L` (D8.9) and `log E e^{uL} = k log Tr ρ^{1-u} ≤ kuS + kC₀𝓑u²`
(D8.5) give `E e^{u(F - kS)} ≤ e^{kC₀𝓑u²}`. -/
theorem step_8_10_1 {ρ : Matrix Ω Ω ℂ} (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) (k : ℕ)
    {u S C : ℝ} (hu : 0 ≤ u) (hu1 : u < 1)
    (hmgf : Real.log (trPowPos ρ hρ.isHermitian u) ≤ u * S + C * u ^ 2) :
    (trace (tensorPow (k := k) ρ * cfc (fun x => Real.exp (1 * u * (x - k * S)))
      (labelObservable (copyPerm Ω k) fun l => Real.log l.dim))).re ≤
        Real.exp (k * C * u ^ 2) := by
  have hρk := posSemidef_tensorPow (k := k) hρ
  have hinv := commute_permOp_copyPerm_tensorPow (k := k) ρ
  have htrk : (tensorPow (k := k) ρ).trace = 1 := by rw [trace_tensorPow, htr, one_pow]
  rw [re_trace_tensorPow_mul_cfc hρ]
  calc _ ≤ ∑ p, Real.exp (-(u * k * S)) *
        ((p.1 : ℝ) ^ (1 - u) * jointMass (copyPerm Ω k) hρk p) := by
        refine Finset.sum_le_sum fun p _ => ?_
        have hm := jointMass_nonneg hρk hinv p
        rcases eq_or_ne (jointMass (copyPerm Ω k) hρk p) 0 with h0 | h0
        · simp [h0]
        rcases (eigenvalue_nonneg hρk p.1).lt_or_eq with hpos | hzero
        · have := log_dim_le_neg_log hρk hinv htrk p h0 hpos
          rw [Real.rpow_def_of_pos hpos]
          calc (p.1 : ℝ) * jointMass (copyPerm Ω k) hρk p *
                Real.exp (1 * u * (Real.log p.2.dim - k * S)) =
                Real.exp (Real.log p.1 + u * Real.log p.2.dim - u * k * S) *
                  jointMass (copyPerm Ω k) hρk p := by
                rw [Real.exp_sub, Real.exp_add, Real.exp_log hpos,
                  show 1 * u * (Real.log p.2.dim - k * S) = u * Real.log p.2.dim - u * k * S by
                  ring, Real.exp_sub]
                ring
            _ ≤ Real.exp (Real.log p.1 * (1 - u) - u * k * S) * jointMass (copyPerm Ω k) hρk p :=
                mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith)) hm
            _ = _ := by rw [sub_eq_add_neg, Real.exp_add]; ring
        · rw [← hzero, Real.zero_rpow (by linarith)]
          simp
    _ = Real.exp (-(u * k * S)) * ∑ p, (p.1 : ℝ) ^ (1 - u) * jointMass (copyPerm Ω k) hρk p := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (-(u * k * S)) * Real.exp (k * (u * S + C * u ^ 2)) := by
        gcongr
        exact sum_rpow_jointMass_tensorPow_le hρ htr k hu1 hmgf
    _ = _ := by rw [← Real.exp_add]; ring_nf

/-- D8.10.2. `-` sign: `e^{-u(F - kS)} = e^{-u(L - kS)} e^{u(L - F)}`; Cauchy–Schwarz,
D8.5 at `-2u` and D8.9 at `b = 2u ≤ 1`:
`(E e^{-u(F - kS)})² ≤ E e^{-2u(L - kS)} E e^{2u(L - F)} ≤ e^{4kC₀𝓑u²} poly(k)`. -/
theorem step_8_10_2 {ρ : Matrix Ω Ω ℂ} (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) (k : ℕ)
    {u S C : ℝ} (hu : 0 ≤ u) (hu1 : 2 * u ≤ 1)
    (hmgf : Real.log (trPowPos ρ hρ.isHermitian (-2 * u)) ≤ -2 * u * S + C * (-2 * u) ^ 2) :
    (trace (tensorPow (k := k) ρ * cfc (fun x => Real.exp (-1 * u * (x - k * S)))
      (labelObservable (copyPerm Ω k) fun l => Real.log l.dim))).re ^ 2 ≤
        Real.exp (4 * k * C * u ^ 2) * ((k + 1) ^ (Fintype.card Ω ^ 2) : ℕ) := by
  have hρk := posSemidef_tensorPow (k := k) hρ
  have hinv := commute_permOp_copyPerm_tensorPow (k := k) ρ
  have htrk : (tensorPow (k := k) ρ).trace = 1 := by rw [trace_tensorPow, htr, one_pow]
  set m := jointMass (copyPerm Ω k) hρk
  have hw : ∀ p, 0 ≤ (p.1 : ℝ) * m p := fun p =>
    mul_nonneg (eigenvalue_nonneg hρk p.1) (jointMass_nonneg hρk hinv p)
  -- first factor: D8.5 at `-2u`
  have hA : ∑ p, (p.1 : ℝ) * m p * Real.exp (-2 * u * (-Real.log p.1 - k * S)) ≤
      Real.exp (4 * k * C * u ^ 2) := by
    calc _ = Real.exp (2 * u * k * S) * ∑ p, (p.1 : ℝ) ^ (1 - -2 * u) * m p := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          rcases (eigenvalue_nonneg hρk p.1).lt_or_eq with hpos | hzero
          · rw [Real.rpow_def_of_pos hpos,
              show Real.log p.1 * (1 - -2 * u) = Real.log p.1 + 2 * u * Real.log p.1 by ring,
              Real.exp_add, Real.exp_log hpos,
              show -2 * u * (-Real.log p.1 - k * S) = 2 * u * Real.log p.1 + 2 * u * k * S by
              ring, Real.exp_add]
            ring
          · rw [← hzero, Real.zero_rpow (by linarith)]
            simp
      _ ≤ Real.exp (2 * u * k * S) * Real.exp (k * (-2 * u * S + C * (-2 * u) ^ 2)) := by
          gcongr
          exact sum_rpow_jointMass_tensorPow_le hρ htr k (by linarith) hmgf
      _ = _ := by rw [← Real.exp_add]; ring_nf
  -- second factor: D8.9 at `b = 2u ≤ 1`
  have hB : ∑ p, (p.1 : ℝ) * m p * Real.exp (2 * u * (-Real.log p.1 - Real.log p.2.dim)) ≤
      ((k + 1) ^ (Fintype.card Ω ^ 2) : ℕ) := by
    have h := (schurSurprisal hρk htrk hinv).2.2.2 (2 * u) hu1
    rw [re_trace_mul_exp_eq_sum hρk hinv] at h
    exact le_of_eq_of_le (Finset.sum_congr rfl fun p _ => by ring) h
  rw [re_trace_tensorPow_mul_cfc hρ]
  refine (Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _
    (fun p _ => mul_nonneg (hw p) (Real.exp_pos _).le)
    (fun p _ => mul_nonneg (hw p) (Real.exp_pos _).le) fun p _ => le_of_eq ?_).trans
    (mul_le_mul hA hB (Finset.sum_nonneg fun p _ => mul_nonneg (hw p) (Real.exp_pos _).le)
      (Real.exp_pos _).le)
  rw [mul_pow, sq (Real.exp _), ← Real.exp_add,
    show -1 * u * (Real.log p.2.dim - k * S) + -1 * u * (Real.log p.2.dim - k * S) =
      -2 * u * (-Real.log p.1 - k * S) + 2 * u * (-Real.log p.1 - Real.log p.2.dim) by ring,
    Real.exp_add]
  ring

/-- D8.10 (`comparator:signed-label-moments`). For an iid marginal `ρ_Q^{⊗k}` satisfying D8.5,
`F_Q` the label operator of `Q^{⊗k}`, `0 ≤ u ≤ c/√𝓑` (`c` small):
`log E exp{± u (F_Q - k S(Q))} ≤ C k 𝓑 u² + O(log(k + 1))`. Only the `O(log(k + 1))` term depends
on the fixed system. -/
theorem step_8_10 : Step_8_10.{u} := by
  intro C₀ c₀ hC₀ hc₀
  -- D8.10.3: `c = min(c₀/2, 1/2)`, so `u ≤ c/√𝓑` gives `u, 2u ≤ c₀/√𝓑` and `2u ≤ 1`
  refine ⟨min (c₀ / 2) (1 / 2), by positivity, fun {Ω} _ _ ρ hρ htr 𝓑 S h𝓑 hmgf => ?_⟩
  refine ⟨0, ((Fintype.card Ω ^ 2 : ℕ) : ℝ) / 2, fun k u hu huc ε hε => ?_⟩
  have hB0 : 0 < Real.sqrt 𝓑 := by linarith [Real.one_le_sqrt.mpr h𝓑]
  rw [le_div_iff₀ hB0] at huc
  have hc₀u : 2 * u ≤ c₀ / Real.sqrt 𝓑 := by
    rw [le_div_iff₀ hB0]; linarith [min_le_left (c₀ / 2) (1 / 2)]
  have hu1 : 2 * u ≤ 1 := by nlinarith [min_le_right (c₀ / 2) (1 / 2), Real.one_le_sqrt.mpr h𝓑]
  have hpos : ∀ g : ℝ → ℝ, (∀ x, 0 < g x) → 0 < (trace (tensorPow (k := k) ρ * cfc g
      (labelObservable (copyPerm Ω k) fun l => Real.log l.dim))).re := fun g hg => by
    rw [re_trace_tensorPow_mul_cfc hρ]
    exact sum_mul_pos_of_sum_eq_one (fun p => mul_nonneg
      (eigenvalue_nonneg (posSemidef_tensorPow hρ) p.1)
      (jointMass_nonneg _ (commute_permOp_copyPerm_tensorPow ρ) p))
      (sum_jointMass_tensorPow hρ htr k) fun p => hg _
  have hlogk : 0 ≤ Real.log ((k : ℝ) + 1) := Real.log_nonneg (by linarith [k.cast_nonneg (α := ℝ)])
  rcases hε with rfl | rfl
  · -- D8.10.1
    have h1 := step_8_10_1 hρ htr k hu (by linarith)
      (hmgf u (by rw [abs_of_nonneg hu]; linarith))
    have := Real.log_le_log (hpos _ fun x => Real.exp_pos _) h1
    rw [Real.log_exp] at this
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (k.cast_nonneg (α := ℝ)) hC₀.le)
      (by linarith : (0 : ℝ) ≤ 𝓑)) (sq_nonneg u),
      mul_nonneg (by positivity : (0 : ℝ) ≤ ((Fintype.card Ω ^ 2 : ℕ) : ℝ) / 2) hlogk]
  · -- D8.10.2
    have h2 := step_8_10_2 hρ htr k hu hu1
      (hmgf (-2 * u) (by rw [abs_of_nonpos (by linarith)]; linarith))
    have := Real.log_le_log (pow_pos (hpos _ fun x => Real.exp_pos _) 2) h2
    rw [Real.log_pow, Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp] at this
    push_cast at this ⊢
    rw [Real.log_pow] at this
    push_cast at this
    linarith

end Moments

/-! ## D8.12 High label -/

section HighLabelSec

/-- `Tr (diag w)^{⊗k} U(τ) = ∑_a ∏_j [a_j = a_{τ j}] w_{a_j}`. -/
theorem trace_tensorPow_diagonal_mul_permOp {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (w : Ω → ℂ) (k : ℕ) (τ : Equiv.Perm (Fin k)) :
    (tensorPow (k := k) (diagonal w) * permOp (copyPerm Ω k) τ).trace =
      ∑ a : Fin k → Ω, ∏ j, if a j = a (τ j) then w (a j) else 0 := by
  rw [tensorPow_diagonal]
  simp only [trace, diag, diagonal_mul, permOp_apply_apply]
  refine Fintype.sum_congr _ _ fun a => ?_
  by_cases h : ∀ j, a j = a (τ j)
  · have ha : copyPerm Ω k τ a = a := funext fun j => by
      rw [copyPerm_apply, h (τ⁻¹ j)]
      simp
    rw [if_pos ha, _root_.mul_one]
    exact Finset.prod_congr rfl fun j _ => (if_pos (h j)).symm
  · push Not at h
    obtain ⟨j, hj⟩ := h
    rw [Finset.prod_eq_zero (f := fun j => if a j = a (τ j) then w (a j) else 0)
      (Finset.mem_univ j) (if_neg hj), if_neg, mul_zero]
    intro ha
    apply hj
    have := congrFun ha (τ j)
    simpa using this

/-- D8.12.2. Exponential Markov with D8.9 at `b = 1/2`: in a permutation-invariant density the
mass of `L - F > t` is at most `poly(k) e^{-t/2}`. -/
theorem step_8_12_2 {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {k : ℕ}
    {ρ : Matrix (Fin k → Ω) (Fin k → Ω) ℂ} (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hinv : ∀ τ, Commute (permOp (copyPerm Ω k) τ) ρ) (t : ℝ) :
    ∑ p, (p.1 : ℝ) * jointMass (copyPerm Ω k) hρ p *
        (if t < -Real.log (p.1 : ℝ) - Real.log p.2.dim then 1 else 0) ≤
      Real.exp (-t / 2) * ((k + 1) ^ (Fintype.card Ω ^ 2) : ℕ) := by
  have h := (schurSurprisal hρ htr hinv).2.2.2 (1 / 2) (by norm_num)
  rw [re_trace_mul_exp_eq_sum hρ hinv] at h
  calc _ ≤ ∑ p, Real.exp (-t / 2) * ((p.1 : ℝ) * Real.exp (1 / 2 * (-Real.log (p.1 : ℝ) -
        Real.log p.2.dim)) * jointMass (copyPerm Ω k) hρ p) := by
        refine Finset.sum_le_sum fun p _ => ?_
        have h0 : 0 ≤ (p.1 : ℝ) * jointMass (copyPerm Ω k) hρ p :=
          mul_nonneg (eigenvalue_nonneg hρ p.1) (jointMass_nonneg hρ hinv p)
        split_ifs with hlt
        · have h1 : 1 ≤ Real.exp (-t / 2) *
              Real.exp (1 / 2 * (-Real.log (p.1 : ℝ) - Real.log p.2.dim)) := by
            rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
          calc (p.1 : ℝ) * jointMass (copyPerm Ω k) hρ p * 1 ≤
                (p.1 : ℝ) * jointMass (copyPerm Ω k) hρ p * (Real.exp (-t / 2) *
                  Real.exp (1 / 2 * (-Real.log (p.1 : ℝ) - Real.log p.2.dim))) :=
                mul_le_mul_of_nonneg_left h1 h0
            _ = _ := by ring
        · rw [mul_zero]
          exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (mul_nonneg
            (eigenvalue_nonneg hρ p.1) (Real.exp_pos _).le) (jointMass_nonneg hρ hinv p))
    _ = Real.exp (-t / 2) * ∑ p, (p.1 : ℝ) * Real.exp (1 / 2 * (-Real.log (p.1 : ℝ) -
        Real.log p.2.dim)) * jointMass (copyPerm Ω k) hρ p := by rw [Finset.mul_sum]
    _ ≤ _ := by gcongr

/-- D8.12.1. Chebyshev for the iid surprisal: for `ρ = diag(w)^{⊗k}` (`w > 0`, `∑ w = 1`, mean
`S = ∑ w (-log w)`), the mass of `|L - kS| > t` is at most `k Var / t²`. -/
theorem step_8_12_1 {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {w : Ω → ℝ} (hw : ∀ i, 0 < w i)
    (hw1 : ∑ i, w i = 1) (k : ℕ)
    (hρ : (tensorPow (k := k) (diagonal fun i => (w i : ℂ))).PosSemidef) {t : ℝ} (ht : 0 < t) :
    ∑ p, (p.1 : ℝ) * jointMass (copyPerm Ω k) hρ p *
        (if t < |-Real.log (p.1 : ℝ) - k * ∑ i, w i * -Real.log (w i)| then 1 else 0) ≤
      k * (∑ i, w i * (-Real.log (w i) - ∑ i', w i' * -Real.log (w i')) ^ 2) / t ^ 2 := by
  have hinv : ∀ τ, Commute (permOp (copyPerm Ω k) τ)
      (tensorPow (k := k) (diagonal fun i => (w i : ℂ))) := fun τ =>
    commute_permOp_copyPerm_tensorPow _ τ
  set μ := ∑ i, w i * -Real.log (w i)
  set f : ℝ → ℝ := fun x => x * if t < |-Real.log x - k * μ| then 1 else 0
  have h1 := re_trace_cfc_eq_sum hρ hinv f
  have hD : tensorPow (k := k) (diagonal fun i => (w i : ℂ)) =
      diagonal fun a : Fin k → Ω => ((∏ j, w (a j) : ℝ) : ℂ) := by
    rw [tensorPow_diagonal]
    congr 1
    funext a
    simp
  have h2 : (cfc f (tensorPow (k := k) (diagonal fun i => (w i : ℂ)))).trace.re =
      ∑ a : Fin k → Ω, f (∏ j, w (a j)) := by
    have hcfc : cfc f (diagonal fun a : Fin k → Ω => ((∏ j, w (a j) : ℝ) : ℂ)) =
        diagonal (RCLike.ofReal ∘ f ∘ fun a : Fin k → Ω => ∏ j, w (a j)) :=
      Matrix.cfc_diagonal (𝕜 := ℂ) _ _
    rw [hD, hcfc, trace_diagonal, Complex.re_sum]
    simp
  calc _ = ∑ p, f (p.1 : ℝ) * jointMass (copyPerm Ω k) hρ p :=
        Finset.sum_congr rfl fun p _ => by simp only [f]; ring
    _ = ∑ a : Fin k → Ω, f (∏ j, w (a j)) := by rw [← h1, h2]
    _ ≤ ∑ a : Fin k → Ω, (∏ j, w (a j)) *
        (if t ≤ |∑ j, -Real.log (w (a j)) - k * μ| then 1 else 0) := by
        refine Finset.sum_le_sum fun a _ => ?_
        have hlog : -Real.log (∏ j, w (a j)) = ∑ j, -Real.log (w (a j)) := by
          rw [Real.log_prod fun j _ => (hw _).ne', Finset.sum_neg_distrib]
        simp only [f, hlog]
        refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun j _ => (hw _).le)
        split_ifs with h h' <;> first | exact le_rfl | exact absurd h.le h' | norm_num
    _ ≤ _ := Finset.sum_prod_iid_indicator_le (fun i => (hw i).le) hw1
        (fun i => -Real.log (w i)) k ht

/-! ### The `R`-marginal of `ψ` -/

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ}

/-- One copy of `𝒱` as its `R`-part and its `(phys, C)`-part. -/
def splitR (d : ℕ) : SiteConfig (dims n d) ≃ Fin d × (SiteConfig n × Fin d) where
  toFun s := (s .R, (physPart s, s .C))
  invFun t f := match f with
    | .phys v => t.2.1 v
    | .C => t.2.2
    | .R => t.1
  left_inv s := by funext f; cases f <;> rfl
  right_inv t := rfl

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem splitR_symm_C (d : ℕ) (t : Fin d × (SiteConfig n × Fin d)) :
    (splitR d).symm t .C = t.2.2 := rfl

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem splitR_symm_R (d : ℕ) (t : Fin d × (SiteConfig n × Fin d)) :
    (splitR d).symm t .R = t.1 := rfl

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem splitR_symm_phys (d : ℕ) (t : Fin d × (SiteConfig n × Fin d)) (v : σ) :
    (splitR d).symm t (.phys v) = t.2.1 v := rfl

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem physPart_splitR_symm (d : ℕ) (t : Fin d × (SiteConfig n × Fin d)) :
    physPart ((splitR d).symm t) = t.2.1 := rfl

/-- `k` copies of `𝒱` as the `R`-parts and the `(phys, C)`-parts of the copies. -/
def splitRCopies (d k : ℕ) :
    (Fin k → Fin d) × (Fin k → SiteConfig n × Fin d) ≃ Transport.Config (dims n d) k where
  toFun t j := (splitR d).symm (t.1 j, t.2 j)
  invFun x := (fun j => x j .R, fun j => (physPart (x j), x j .C))
  left_inv _ := rfl
  right_inv x := funext fun j => (splitR d).symm_apply_apply (x j)

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem splitRCopies_apply (d k : ℕ)
    (t : (Fin k → Fin d) × (Fin k → SiteConfig n × Fin d)) (j : Fin k) :
    splitRCopies d k t j = (splitR d).symm (t.1 j, t.2 j) := rfl

/-- `⟨φ^{⊗k}, U_R(τ) φ^{⊗k}⟩ = ∑_a ∏_j M(a_j, a_{τ j})`, `M` the `R`-overlap of `φ`. -/
theorem star_tensorVec_dotProduct_permOp_R (d k : ℕ) (φ : SiteConfig (dims n d) → ℂ)
    (τ : Equiv.Perm (Fin k)) :
    star (tensorVec k φ) ⬝ᵥ
        (permOp (Replicas.copyPerm (fun f => Fin (dims n d f)) k {Site.R}) τ *ᵥ tensorVec k φ) =
      ∑ a : Fin k → Fin d, ∏ j, ∑ t, star (φ ((splitR d).symm (a j, t))) *
        φ ((splitR d).symm (a (τ j), t)) := by
  rw [permOp_mulVec, ← map_inv]
  simp only [dotProduct, Pi.star_apply, Function.comp_apply, tensorVec, star_prod]
  rw [← (splitRCopies d k).sum_comp, Fintype.sum_prod_type]
  refine Fintype.sum_congr _ _ fun a => ?_
  rw [Fintype.prod_sum]
  refine Fintype.sum_congr _ _ fun t => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hc : ∀ (x : Transport.Config (dims n d) k) (f : Site σ),
      (Replicas.copyPerm (fun f => Fin (dims n d f)) k {Site.R} τ).symm x j f =
        if f ∈ ({Site.R} : Finset (Site σ)) then x (τ j) f else x j f := fun x f => by
    rw [← Equiv.Perm.inv_def, ← map_inv, Replicas.copyPerm_apply, inv_inv]
  congr 2
  funext f
  cases f <;> simp [hc] <;> rfl

variable {D : PhysData n} {X : Finset σ}

omit [Fintype σ] in
theorem restrictX_replaceX (x : SiteConfig n) (y : Reg (fun v => Fin (n v)) X) :
    restrictX (replaceX x y) = y := by
  funext v
  simp [restrictX, replaceX, v.2]

omit [Fintype σ] in
theorem replaceX_replaceX_restrictX (x : SiteConfig n) (y : Reg (fun v => Fin (n v)) X) :
    replaceX (replaceX x y) (restrictX (X := X) x) = x := by
  funext v
  by_cases hv : v ∈ X <;> simp [restrictX, replaceX, hv]

/-- For `g` ignoring the `X`-part: `dim 𝓗_X ∑_x h(x_X) g(x) = (∑_y h(y)) (∑_x g(x))`. -/
theorem dimReg_mul_sum_restrictX_mul (h : Reg (fun v => Fin (n v)) X → ℂ)
    (g : SiteConfig n → ℂ) (hg : ∀ (x : SiteConfig n) (y : Reg (fun v => Fin (n v)) X),
      g (replaceX x y) = g x) :
    (dimReg n X : ℂ) * ∑ x, h (restrictX x) * g x = (∑ y, h y) * ∑ x, g x := by
  have hΦ : Function.Involutive fun q : SiteConfig n × Reg (fun v => Fin (n v)) X =>
      (replaceX q.1 q.2, restrictX q.1) := fun q =>
    Prod.ext (replaceX_replaceX_restrictX q.1 q.2) (restrictX_replaceX q.1 q.2)
  have hcard : (dimReg n X : ℂ) = Fintype.card (Reg (fun v => Fin (n v)) X) := by
    rw [Fintype.card_pi, Finset.prod_coe_sort X fun v => Fintype.card (Fin (n v))]
    simp [dimReg]
  calc (dimReg n X : ℂ) * ∑ x, h (restrictX x) * g x =
        ∑ q : SiteConfig n × Reg (fun v => Fin (n v)) X, h (restrictX q.1) * g q.1 := by
        rw [Fintype.sum_prod_type, hcard, Finset.mul_sum]
        simp
    _ = ∑ q : SiteConfig n × Reg (fun v => Fin (n v)) X, h q.2 * g q.1 :=
        (Equiv.sum_comp (Function.Involutive.toPerm _ hΦ)
          (fun q => h (restrictX q.1) * g q.1)).symm.trans
          (Fintype.sum_congr _ _ fun q => by simp [restrictX_replaceX, hg])
    _ = _ := by
        rw [Fintype.sum_prod_type, Finset.sum_mul_sum, Finset.sum_comm]

/-- D8.12.1. The `R`-overlap of one copy of `post`: `∑_{phys, C} \overline{φ(a, ·)} φ(b, ·) =
δ_{ab} p'_a` (`w_i` orthonormal, `|i⟩_X` normalized). -/
theorem sum_star_post1_mul_post1 (h11 : Step_8_11.{u}) (E : TypicalSet D X) [∀ v, NeZero (n v)]
    (a b : Fin E.d) :
    ∑ t, star (BXC E ((splitR E.d).symm (a, t)) * ψ E ((splitR E.d).symm (a, t))) *
        (BXC E ((splitR E.d).symm (b, t)) * ψ E ((splitR E.d).symm (b, t))) =
      if a = b then (E.p' (E.idx a).1 : ℂ) else 0 := by
  obtain ⟨-, hW, hON, -, -⟩ := h11 D X
  have hd : (0 : ℝ) < E.d := by exact_mod_cast E.nonempty.card_pos
  have hp : ∀ c : Fin E.d, 0 < D.p X (E.idx c).1 := fun c =>
    (Real.exp_pos _).trans_le (E.lower _ (E.idx c).2)
  have hz : 0 < E.z :=
    Finset.sum_pos (fun i hi => (Real.exp_pos _).trans_le (E.lower i hi)) E.nonempty
  have hp' : ∀ c : Fin E.d, 0 ≤ E.p' (E.idx c).1 := fun c => (div_pos (hp c) hz).le
  have hdim : (dimReg n X : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun v _ => NeZero.ne _)
  set K : ℝ := (Real.sqrt E.d)⁻¹ * (Real.sqrt E.d)⁻¹ * Real.sqrt (E.p' (E.idx a).1) *
    Real.sqrt (E.p' (E.idx b).1)
  set hX : Reg (fun v => Fin (n v)) X → ℂ := fun y =>
    ∑ c : Fin E.d, star (schmidtX (D := D) (E.idx c).1 y) * schmidtX (D := D) (E.idx c).1 y
  set g : SiteConfig n → ℂ := fun x =>
    star (schmidtW (D := D) (E.idx a).1 x) * schmidtW (D := D) (E.idx b).1 x
  have e1 : ∀ t : SiteConfig n × Fin E.d,
      star (BXC E ((splitR E.d).symm (a, t)) * ψ E ((splitR E.d).symm (a, t))) *
        (BXC E ((splitR E.d).symm (b, t)) * ψ E ((splitR E.d).symm (b, t))) =
      (K : ℂ) * (star (schmidtX (D := D) (E.idx t.2).1 (restrictX t.1)) *
        schmidtX (D := D) (E.idx t.2).1 (restrictX t.1)) * g t.1 := by
    intro t
    simp only [BXC, ψ, splitR_symm_C, splitR_symm_R, physPart_splitR_symm, star_mul',
      Complex.star_def, Complex.conj_ofReal, K, g]
    push_cast
    ring
  have e2 : ∑ t : SiteConfig n × Fin E.d, (K : ℂ) *
      (star (schmidtX (D := D) (E.idx t.2).1 (restrictX t.1)) *
        schmidtX (D := D) (E.idx t.2).1 (restrictX t.1)) * g t.1 =
      K * ∑ x, hX (restrictX x) * g x := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [hX, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  have hXsum : ∑ y, hX y = E.d := by
    simp only [hX]
    rw [Finset.sum_comm]
    have h1 : ∀ c : Fin E.d, ∑ y, star (schmidtX (D := D) (E.idx c).1 y) *
        schmidtX (D := D) (E.idx c).1 y = 1 := fun c =>
      (D.isHermitian_ρ X).star_eigenvectorBasis_dotProduct_self (E.idx c).1
    rw [Finset.sum_congr rfl fun c _ => h1 c]
    simp
  have hgsum : ∑ x, g x = if a = b then (dimReg n X : ℂ) else 0 := by
    have h := hON (E.idx a).1 (E.idx b).1 (hp a) (hp b)
    have hab : ((E.idx a).1 = (E.idx b).1) ↔ a = b :=
      Subtype.ext_iff.symm.trans E.idx.injective.eq_iff
    simp only [hab] at h
    exact h
  have hsplit := dimReg_mul_sum_restrictX_mul hX g fun x y => by simp only [g, hW]
  rw [hXsum, hgsum] at hsplit
  have hS : ∑ x, hX (restrictX x) * g x = if a = b then (E.d : ℂ) else 0 := by
    rw [eq_comm, ← mul_right_inj' hdim, hsplit]
    split_ifs <;> ring
  simp_rw [e1]
  rw [e2, hS]
  split_ifs with hab
  · subst hab
    have hK : K * E.d = E.p' (E.idx a).1 := by
      simp only [K]
      rw [mul_assoc ((Real.sqrt E.d)⁻¹ * (Real.sqrt E.d)⁻¹), Real.mul_self_sqrt (hp' a),
        ← mul_inv, Real.mul_self_sqrt hd.le]
      field_simp
    exact_mod_cast hK
  · simp

/-- D8.12.1. The `R`-marginal `diag(p'_i)_{i ∈ E}` of `ψ`. -/
noncomputable def rhoR (E : TypicalSet D X) : Matrix (Fin E.d) (Fin E.d) ℂ :=
  diagonal fun c => (E.p' (E.idx c).1 : ℂ)

/-- The label mass of a product vector on `k` copies of `𝒱` whose `R`-overlap is diagonal,
`∑_{phys, C} \overline{φ(a, ·)} φ(b, ·) = δ_{ab} w_a`: `‖π^λ_R φ^{⊗k}‖² = Tr diag(w)^{⊗k} π^λ`. -/
theorem star_piR_dotProduct_piR_tensorVec (d k : ℕ) (φ : SiteConfig (dims n d) → ℂ)
    (w : Fin d → ℂ) (hM : ∀ a b, ∑ t, star (φ ((splitR d).symm (a, t))) *
      φ ((splitR d).symm (b, t)) = if a = b then w a else 0)
    (l : IrrepLabel (Equiv.Perm (Fin k))) :
    star (piR d k l *ᵥ tensorVec k φ) ⬝ᵥ (piR d k l *ᵥ tensorVec k φ) =
      trace (tensorPow (k := k) (diagonal w) * labelProj (copyPerm (Fin d) k) l) := by
  have key : ∀ τ : Equiv.Perm (Fin k), star (tensorVec k φ) ⬝ᵥ
      (permOp (Replicas.copyPerm (fun f => Fin (dims n d f)) k {Site.R}) τ *ᵥ tensorVec k φ) =
      (tensorPow (k := k) (diagonal w) * permOp (copyPerm (Fin d) k) τ).trace := fun τ => by
    rw [star_tensorVec_dotProduct_permOp_R, trace_tensorPow_diagonal_mul_permOp]
    exact Fintype.sum_congr _ _ fun a => Finset.prod_congr rfl fun j _ => hM (a j) (a (τ j))
  have hP := isHermitian_labelProj (Replicas.copyPerm (fun f => Fin (dims n d f)) k {Site.R}) l
  simp only [piR, Replicas.π]
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hP.eq, labelProj_mul_self, labelProj,
    labelProj, groupAlgebraRep_eq_sum, groupAlgebraRep_eq_sum, sum_mulVec, dotProduct_sum,
    Matrix.mul_sum, trace_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [smul_mulVec, dotProduct_smul, mul_smul_comm, trace_smul, key]

/-- D8.12.1. The label probability is the iid one of the `R`-marginal:
`q_k(λ) = ‖π^λ_R post_k‖² = Tr ρ_R^{⊗k} π^λ`. -/
theorem q_eq_re_trace (h11 : Step_8_11.{u}) [∀ v, NeZero (n v)] (E : TypicalSet D X) (k : ℕ)
    (l : IrrepLabel (Equiv.Perm (Fin k))) :
    q E k l = (trace (tensorPow (k := k) (rhoR E) * labelProj (copyPerm (Fin E.d) k) l)).re := by
  rw [q, post, rhoR, star_piR_dotProduct_piR_tensorVec E.d k _ _ (sum_star_post1_mul_post1 h11 E)]

/-- D8.12.3. `V/√k + (k + 1)^m e^{-k^{3/4}/2} ≤ 1/2` for large `k`. -/
theorem eventually_tail_le_half (V : ℝ) (m : ℕ) :
    ∀ᶠ k : ℕ in atTop, 1 ≤ k ∧
      V / Real.sqrt k + (((k + 1) ^ m : ℕ) : ℝ) * Real.exp (-((k : ℝ) ^ (3 / 4 : ℝ)) / 2) ≤
        1 / 2 := by
  have hpower : Tendsto (fun k : ℕ => (k : ℝ) ^ (3 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (3 / 4 : ℝ))).comp tendsto_natCast_atTop_atTop
  have hdecay : Tendsto (fun k : ℕ => (k : ℝ) ^ m *
      Real.exp (-((k : ℝ) ^ (3 / 4 : ℝ)) / 2)) atTop (𝓝 0) := by
    refine ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (4 * (m : ℝ) / 3) (1 / 2)
      (by norm_num)).comp hpower).congr' (Eventually.of_forall fun k => ?_)
    dsimp only [Function.comp_apply]
    rw [← Real.rpow_mul (Nat.cast_nonneg k),
      show (3 / 4 : ℝ) * (4 * (m : ℝ) / 3) = (m : ℝ) by ring, Real.rpow_natCast,
      show -(1 / 2 : ℝ) * (k : ℝ) ^ (3 / 4 : ℝ) = -((k : ℝ) ^ (3 / 4 : ℝ)) / 2 by ring]
  have hroot : Tendsto (fun k : ℕ => Real.sqrt (k : ℝ)) atTop atTop := by
    simpa only [Real.sqrt_eq_rpow, Function.comp_def] using
      (tendsto_rpow_atTop (by norm_num : 0 < (1 / 2 : ℝ))).comp tendsto_natCast_atTop_atTop
  have hsum : Tendsto (fun k : ℕ => V / Real.sqrt (k : ℝ) +
      (2 : ℝ) ^ m * ((k : ℝ) ^ m * Real.exp (-((k : ℝ) ^ (3 / 4 : ℝ)) / 2))) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add] using
      (hroot.const_div_atTop V).add (hdecay.const_mul ((2 : ℝ) ^ m))
  filter_upwards [eventually_ge_atTop 1,
    hsum.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with k hk hsumk
  have hcoeff : (((k + 1) ^ m : ℕ) : ℝ) ≤ (2 : ℝ) ^ m * (k : ℝ) ^ m := by
    rw [Nat.cast_pow, Nat.cast_add, Nat.cast_one, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast (show k + 1 ≤ 2 * k by omega)) m
  refine ⟨hk, le_trans ?_ hsumk.le⟩
  simpa only [_root_.mul_assoc] using
    add_le_add_right (mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos _).le) (V / Real.sqrt k)

/-- D8.12.3. With probability `≥ 1/2` (for `k` with `V/√k + poly(k) e^{-k^{3/4}/2} ≤ 1/2`):
`|F - kS| ≤ 2k^{3/4}`, since `F ≤ L` and `|F - kS| > 2k^{3/4}` forces `|L - kS| > k^{3/4}`
(D8.12.1) or `L - F > k^{3/4}` (D8.12.2). -/
theorem step_8_12_3 {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {w : Ω → ℝ} (hw : ∀ i, 0 < w i)
    (hw1 : ∑ i, w i = 1) {S : ℝ} (hS : ∑ i, w i * -Real.log (w i) = S) {k : ℕ}
    (hk : 1 ≤ k ∧ (∑ i, w i * (-Real.log (w i) - ∑ i', w i' * -Real.log (w i')) ^ 2) /
        Real.sqrt k + (((k + 1) ^ (Fintype.card Ω ^ 2) : ℕ) : ℝ) *
          Real.exp (-((k : ℝ) ^ (3 / 4 : ℝ)) / 2) ≤ 1 / 2) :
    1 / 2 ≤ ∑ l, (if |Real.log l.dim - k * S| ≤ 2 * (k : ℝ) ^ (3 / 4 : ℝ) then 1 else 0) *
      (trace (tensorPow (k := k) (diagonal fun i => (w i : ℂ)) *
        labelProj (copyPerm Ω k) l)).re := by
  subst hS
  set S := ∑ i, w i * -Real.log (w i)
  obtain ⟨hk1, htail⟩ := hk
  set ρ := tensorPow (k := k) (diagonal fun i => (w i : ℂ))
  have hρ : ρ.PosSemidef :=
    posSemidef_tensorPow (PosSemidef.diagonal fun c => Complex.zero_le_real.mpr (hw c).le)
  have htr : ρ.trace = 1 := by
    rw [trace_tensorPow, trace_diagonal, ← Complex.ofReal_sum, hw1]; simp
  have hinv : ∀ τ, Commute (permOp (copyPerm Ω k) τ) ρ := fun τ =>
    commute_permOp_copyPerm_tensorPow _ τ
  set t := (k : ℝ) ^ (3 / 4 : ℝ)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have ht : 0 < t := Real.rpow_pos_of_pos hk0 _
  set V := ∑ i, w i * (-Real.log (w i) - ∑ i', w i' * -Real.log (w i')) ^ 2
  -- D8.12.1
  have hA := step_8_12_1 hw hw1 k hρ ht
  -- D8.12.2
  have hB := step_8_12_2 hρ htr hinv t
  have hkV : (k : ℝ) * V / t ^ 2 = V / Real.sqrt k := by
    have h2 : t ^ 2 = (k : ℝ) * Real.sqrt k := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hk0.le, Real.sqrt_eq_rpow,
        ← Real.rpow_one_add' hk0.le (by norm_num)]
      norm_num
    rw [h2, mul_div_mul_left V _ hk0.ne']
  have hbad : ∑ l, (if 2 * t < |Real.log l.dim - k * S| then 1 else 0) *
      (trace (ρ * labelProj (copyPerm Ω k) l)).re ≤ 1 / 2 := by
    rw [sum_mul_re_trace_mul_labelProj_eq_sum hρ hinv]
    calc _ ≤ ∑ p, ((p.1 : ℝ) * jointMass (copyPerm Ω k) hρ p *
            (if t < |-Real.log (p.1 : ℝ) - k * S| then 1 else 0) +
          (p.1 : ℝ) * jointMass (copyPerm Ω k) hρ p *
            (if t < -Real.log (p.1 : ℝ) - Real.log p.2.dim then 1 else 0)) := by
          refine Finset.sum_le_sum fun p _ => ?_
          have h0 : 0 ≤ (p.1 : ℝ) * jointMass (copyPerm Ω k) hρ p :=
            mul_nonneg (eigenvalue_nonneg hρ p.1) (jointMass_nonneg hρ hinv p)
          have hA0 : 0 ≤ (p.1 : ℝ) * jointMass (copyPerm Ω k) hρ p *
              (if t < |-Real.log (p.1 : ℝ) - k * S| then 1 else 0) :=
            mul_nonneg h0 (by split_ifs <;> norm_num)
          have hB0 : 0 ≤ (p.1 : ℝ) * jointMass (copyPerm Ω k) hρ p *
              (if t < -Real.log (p.1 : ℝ) - Real.log p.2.dim then 1 else 0) :=
            mul_nonneg h0 (by split_ifs <;> norm_num)
          by_cases hb : 2 * t < |Real.log p.2.dim - k * S|
          · rw [if_pos hb]
            rcases eq_or_ne (jointMass (copyPerm Ω k) hρ p) 0 with hm0 | hm0
            · simp [hm0]
            rcases (eigenvalue_nonneg hρ p.1).lt_or_eq with hpos | hzero
            · have hr := log_dim_le_neg_log hρ hinv htr p hm0 hpos
              by_cases ha : t < |-Real.log (p.1 : ℝ) - k * S|
              · rw [if_pos ha]; linarith
              · have hB' : t < -Real.log (p.1 : ℝ) - Real.log p.2.dim := by
                  by_contra hB'
                  push Not at ha hB'
                  have := abs_le.mp ha
                  exact absurd (abs_le.mpr ⟨by linarith, by linarith⟩) (not_le.mpr hb)
                rw [if_neg ha, if_pos hB']; linarith
            · simp [← hzero]
          · rw [if_neg hb, mul_zero]; linarith
      _ = _ := Finset.sum_add_distrib
      _ ≤ k * V / t ^ 2 + Real.exp (-t / 2) * ((k + 1) ^ (Fintype.card Ω ^ 2) : ℕ) :=
          add_le_add hA hB
      _ ≤ 1 / 2 := by rw [hkV]; linarith
  have hP1 : ∑ l, (trace (ρ * labelProj (copyPerm Ω k) l)).re = 1 := by
    rw [← Complex.re_sum, ← trace_sum, ← Matrix.mul_sum, sum_labelProj, Matrix.mul_one, htr]
    simp
  have hsplit : ∀ l : IrrepLabel (Equiv.Perm (Fin k)),
      (if |Real.log l.dim - k * S| ≤ 2 * t then (1 : ℝ) else 0) =
        1 - if 2 * t < |Real.log l.dim - k * S| then 1 else 0 := fun l => by
    by_cases h1 : |Real.log l.dim - k * S| ≤ 2 * t
    · rw [if_pos h1, if_neg (not_lt.mpr h1)]; norm_num
    · rw [if_neg h1, if_pos (not_le.mp h1)]; norm_num
  simp only [hsplit, sub_mul, _root_.one_mul, Finset.sum_sub_distrib]
  rw [hP1]
  linarith

/-- D8.12.4. At most `(k + 1)^{q²}` labels occur on `(ℂ^q)^{⊗k}` (Lemma 6.1 (1)); by pigeonhole a
label in a window of probability `≥ 1/2` has probability `≥ (k + 1)^{-q²}/2`. -/
theorem step_8_12_4 {q k : ℕ} {P : IrrepLabel (Equiv.Perm (Fin k)) → ℝ}
    {good : IrrepLabel (Equiv.Perm (Fin k)) → Prop} [DecidablePred good]
    (hPz : ∀ l, labelProj (copyPerm (Fin q) k) l = 0 → P l = 0)
    (hwin : 1 / 2 ≤ ∑ l, (if good l then 1 else 0) * P l) :
    ∃ l, good l ∧ 1 / 2 / (((k + 1) ^ (q ^ 2) : ℕ) : ℝ) ≤ P l := by
  set G := Finset.univ.filter fun l => good l ∧ labelProj (copyPerm (Fin q) k) l ≠ 0
  have hG : ∑ l ∈ G, P l = ∑ l, (if good l then 1 else 0) * P l := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hg : good l <;> by_cases hz : labelProj (copyPerm (Fin q) k) l = 0 <;>
      simp [hg, hz, hPz]
  have hcard : (G.card : ℝ) ≤ (((k + 1) ^ (q ^ 2) : ℕ) : ℝ) := by
    refine Nat.cast_le.mpr ((Finset.card_le_card fun l hl => ?_).trans
      (Replicas.lemma_6_1_1 k q).2.1)
    simp only [G, Finset.mem_filter] at hl ⊢
    exact ⟨hl.1, hl.2.2⟩
  have hne : G.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.sum_empty] at hG
    linarith
  have hN : (0 : ℝ) < (((k + 1) ^ (q ^ 2) : ℕ) : ℝ) := by positivity
  obtain ⟨l, hl, hle⟩ := Finset.exists_le_of_sum_le hne
    (f := fun _ => 1 / 2 / (((k + 1) ^ (q ^ 2) : ℕ) : ℝ)) (g := P) (by
      rw [Finset.sum_const, nsmul_eq_mul, hG]
      calc (G.card : ℝ) * (1 / 2 / (((k + 1) ^ (q ^ 2) : ℕ) : ℝ)) ≤
            (((k + 1) ^ (q ^ 2) : ℕ) : ℝ) * (1 / 2 / (((k + 1) ^ (q ^ 2) : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = 1 / 2 := by field_simp
        _ ≤ _ := hwin)
  exact ⟨l, (Finset.mem_filter.mp hl).2.1, hle⟩

/-- The `R`-marginal `diag(p'_i)_{i ∈ E}` is a probability vector with positive entries and
entropy `S'`. -/
theorem rhoR_spec (E : TypicalSet D X) :
    (∀ c, 0 < E.p' (E.idx c).1) ∧ ∑ c, E.p' (E.idx c).1 = 1 ∧
      ∑ c, E.p' (E.idx c).1 * -Real.log (E.p' (E.idx c).1) = E.S' := by
  have hz : 0 < E.z :=
    Finset.sum_pos (fun i hi => (Real.exp_pos _).trans_le (E.lower i hi)) E.nonempty
  have hsumE : ∀ f : Reg (fun v => Fin (n v)) X → ℝ, ∑ c : Fin E.d, f (E.idx c).1 =
      ∑ i ∈ E.E, f i := fun f => by
    rw [← Finset.sum_coe_sort E.E]; exact E.idx.sum_comp fun i => f i.1
  refine ⟨fun c => div_pos ((Real.exp_pos _).trans_le (E.lower _ (E.idx c).2)) hz, ?_, ?_⟩
  · rw [hsumE E.p']; simp only [TypicalSet.p', ← Finset.sum_div]; exact div_self hz.ne'
  · rw [hsumE fun i => E.p' i * -Real.log (E.p' i)]
    exact Finset.sum_congr rfl fun i _ => by rw [Real.negMulLog]; ring

/-- A label sequence chosen in the window `|log d_λ - kS'| ≤ 2k^{3/4}` with probability
`≥ (k + 1)^{-N}/2` for `k ≥ K₀` (and positive probability for `k < K₀`) is high. -/
theorem highLabel_of_window (E : TypicalSet D X) {P : ∀ k, IrrepLabel (Equiv.Perm (Fin k)) → ℝ}
    (hq : ∀ k l, q E k l = P k l) {K₀ N : ℕ} (hK₀ : ∀ k, K₀ ≤ k → 1 ≤ k)
    (hsel : ∀ k, K₀ ≤ k → ∃ l, |Real.log l.dim - k * E.S'| ≤ 2 * (k : ℝ) ^ (3 / 4 : ℝ) ∧
      1 / 2 / (((k + 1) ^ N : ℕ) : ℝ) ≤ P k l)
    (hpos : ∀ k, ∃ l, 0 < P k l) : ∃ l, HighLabel E l := by
  choose lbig hlbig using hsel
  choose lpos hlpos using hpos
  let l : ∀ k, IrrepLabel (Equiv.Perm (Fin k)) := fun k =>
    if h : K₀ ≤ k then lbig k h else lpos k
  have hsmall : ∀ k, k < K₀ → 0 < P k (l k) := fun k hk => by
    simp only [l, dif_neg (not_le.mpr hk)]; exact hlpos k
  obtain ⟨c₁, hc₁, hc₁le⟩ : ∃ c₁ > 0, ∀ k < K₀, c₁ ≤ P k (l k) := by
    rcases Nat.eq_zero_or_pos K₀ with h0 | h0
    · exact ⟨1, one_pos, fun k hk => absurd hk (by omega)⟩
    obtain ⟨k₀, hk₀, hmin⟩ := (Finset.range K₀).exists_min_image (fun k => P k (l k))
      ⟨0, Finset.mem_range.mpr h0⟩
    exact ⟨_, hsmall k₀ (Finset.mem_range.mp hk₀), fun k hk => hmin k (Finset.mem_range.mpr hk)⟩
  refine ⟨l, min (1 / 2) c₁, (N : ℝ), lt_min (by norm_num) hc₁,
    fun k => if K₀ ≤ k then 2 * (k : ℝ) ^ (-(1 / 4 : ℝ)) else |Real.log (l k).dim - k * E.S'| / k,
    ?_, fun k => ⟨?_, ?_⟩⟩
  · have h := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      tendsto_natCast_atTop_atTop).const_mul 2
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop K₀] with k hk
    simp [hk]
  · rw [hq]
    have hk1 : (1 : ℝ) ≤ k + 1 := by linarith [k.cast_nonneg (α := ℝ)]
    by_cases hk : K₀ ≤ k
    · simp only [l, dif_pos hk]
      refine le_trans ?_ (hlbig k hk).2
      rw [Real.rpow_neg (by linarith), Real.rpow_natCast, ← div_eq_mul_inv]
      push_cast
      exact div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)
    · calc _ ≤ min (1 / 2) c₁ * 1 := mul_le_mul_of_nonneg_left
            (Real.rpow_le_one_of_one_le_of_nonpos hk1 (by simp)) (le_min (by norm_num) hc₁.le)
        _ ≤ c₁ := by rw [_root_.mul_one]; exact min_le_right _ _
        _ ≤ _ := hc₁le k (not_le.mp hk)
  · by_cases hk : K₀ ≤ k
    · have hk1 : (0 : ℝ) < k := by exact_mod_cast hK₀ k hk
      simp only [l, dif_pos hk, if_pos hk]
      refine (hlbig k hk).1.trans_eq ?_
      rw [show (2 : ℝ) * (k : ℝ) ^ (3 / 4 : ℝ) = 2 * (k ^ (1 : ℝ) * k ^ (-(1 / 4 : ℝ))) by
        rw [← Real.rpow_add hk1]; norm_num, Real.rpow_one]
      ring
    · simp only [if_neg hk]
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0
        simp [IrrepLabel.dim_eq_one]
      · rw [mul_div_cancel₀ _ (by exact_mod_cast h0.ne')]

/-- D8.12 (`comparator:high-label`). One can select `λ_k ⊢ k` (at most `d_*` rows) with
`q_k := ‖π^{λ_k}_R ψ^{⊗k}‖² ≥ poly(k)^{-1}`, `log d_{λ_k} = kS' + o(k)`. -/
theorem step_8_12 (h11 : Step_8_11.{u}) : Step_8_12.{u} := by
  intro σ _ _ n _ D X E
  obtain ⟨hw, hw1, hS'⟩ := rhoR_spec E
  set P : ∀ k, IrrepLabel (Equiv.Perm (Fin k)) → ℝ := fun k l =>
    (trace (tensorPow (k := k) (rhoR E) * labelProj (copyPerm (Fin E.d) k) l)).re with hPdef
  -- D8.12.1: the label probability is that of the iid `R`-marginal `diag(p'_i)^{⊗k}`
  have hq : ∀ k l, q E k l = P k l := q_eq_re_trace h11 E
  have hP1 : ∀ k, ∑ l, P k l = 1 := fun k => by
    simp only [hPdef]
    rw [← Complex.re_sum, ← trace_sum, ← Matrix.mul_sum, sum_labelProj, Matrix.mul_one,
      trace_tensorPow, rhoR, trace_diagonal, ← Complex.ofReal_sum, hw1]
    simp
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp (eventually_tail_le_half (∑ c, E.p' (E.idx c).1 *
    (-Real.log (E.p' (E.idx c).1) - ∑ c', E.p' (E.idx c').1 * -Real.log (E.p' (E.idx c').1)) ^ 2)
    (E.d ^ 2))
  -- D8.12.1–3: for `k ≥ K₀`, `|F_R - kS'| ≤ 2k^{3/4}` with probability `≥ 1/2`
  have hwin : ∀ k, K₀ ≤ k → 1 / 2 ≤ ∑ l, (if |Real.log l.dim - k * E.S'| ≤
      2 * (k : ℝ) ^ (3 / 4 : ℝ) then 1 else 0) * P k l := fun k hk =>
    step_8_12_3 hw hw1 hS' (by rw [Fintype.card_fin]; exact hK₀ k hk)
  -- D8.12.4: at most `(k + 1)^{d_*²}` labels; pigeonhole
  refine highLabel_of_window E hq (N := E.d ^ 2) (fun k hk => (hK₀ k hk).1) (fun k hk =>
    step_8_12_4 (q := E.d)
      (good := fun l => |Real.log l.dim - k * E.S'| ≤ 2 * (k : ℝ) ^ (3 / 4 : ℝ))
      (fun l h0 => by simp [hPdef, h0]) (hwin k hk)) fun k => ?_
  by_contra h
  push Not at h
  linarith [hP1 k, Finset.sum_nonpos fun l (_ : l ∈ Finset.univ) => h l]

end HighLabelSec

/-! ## D8.13 The prevector -/

section PrevectorSec

/-- `X` commutes with `A^r` whenever it commutes with `A` (any real `r`, any `A`). -/
theorem commute_rpow_of_commute {m : Type*} [Fintype m] [DecidableEq m] {X A : Matrix m m ℂ}
    (h : Commute X A) (r : ℝ) : Commute X (A ^ r) := by
  rw [CFC.rpow_def]
  exact (Commute.cfc_nnreal h.symm _).symm

/-- `X` commutes with `A #_p B` whenever it commutes with `A` and `B`. -/
theorem commute_geomMean_of_commute {m : Type*} [Fintype m] [DecidableEq m]
    {X A B : Matrix m m ℂ} (hA : Commute X A) (hB : Commute X B) (p : ℝ) :
    Commute X (geomMean p A B) := by
  have ha := commute_rpow_of_commute hA
  exact ((ha _).mul_right (commute_rpow_of_commute (((ha _).mul_right hB).mul_right (ha _))
    p)).mul_right (ha _)

/-- D8.13.4 (tree). `X` commutes with the root of a mean tree whose leaves it commutes with. -/
theorem commute_eval_of_commute {m : Type*} [Fintype m] [DecidableEq m] {ι : Type*}
    {A : ι → Matrix m m ℂ} {X : Matrix m m ℂ} (hX : ∀ j, Commute X (A j))
    (T : Transport.MeanTree ι) : Commute X (T.eval A) := by
  induction T with
  | leaf j => exact hX j
  | node p l r ihl ihr => exact commute_geomMean_of_commute ihl ihr p

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {n : σ → ℕ}

omit [DecidableEq σ] in
theorem phys_mem_physReg (v : σ) : Site.phys v ∈ physReg (Finset.univ : Finset σ) :=
  Finset.mem_map_of_mem _ (Finset.mem_univ v)

omit [Fintype σ] [DecidableEq σ] in
theorem C_not_mem_physReg (Q : Finset σ) : Site.C ∉ physReg Q := by simp [physReg]

omit [Fintype σ] [DecidableEq σ] in
theorem R_not_mem_physReg (Q : Finset σ) : Site.R ∉ physReg Q := by simp [physReg]

theorem compl_C : ({Site.C} : Finset (Site σ))ᶜ = physReg Finset.univ ∪ {Site.R} := by
  ext f
  cases f with
  | phys v => simp [phys_mem_physReg v]
  | C => simp [physReg]
  | R => simp

theorem compl_R : ({Site.R} : Finset (Site σ))ᶜ = physReg Finset.univ ∪ {Site.C} := by
  ext f
  cases f with
  | phys v => simp [phys_mem_physReg v]
  | C => simp
  | R => simp [physReg]

variable (D : PhysData n) (d : ℕ)

/-- D8.13.1. The `R`-overlap of `Ω̃ ⊗ Bell_{CR}`: the `R`-marginal of `Bell` is `1/d_*`. -/
theorem sum_star_preVec_mul_preVec [NeZero d] (a b : Fin d) :
    ∑ t, star (preVec D d ((splitR d).symm (a, t))) * preVec D d ((splitR d).symm (b, t)) =
      if a = b then ((d : ℂ))⁻¹ else 0 := by
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have e : ∀ t : SiteConfig n × Fin d, star (preVec D d ((splitR d).symm (a, t))) *
      preVec D d ((splitR d).symm (b, t)) =
      (star (D.Ω t.1) * D.Ω t.1) * (star (bell d t.2 a) * bell d t.2 b) := fun t => by
    simp only [preVec, physPart_splitR_symm, splitR_symm_C, splitR_symm_R, star_mul']
    ring
  have hΩ : ∑ x, star (D.Ω x) * D.Ω x = 1 := D.norm_Ω
  rw [Fintype.sum_prod_type]
  simp_rw [e, ← Finset.mul_sum, ← Finset.sum_mul, hΩ, _root_.one_mul]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, Finset.sum_eq_single a (fun c _ hc => by simp [bell, hc]) (by simp)]
    simp only [bell, if_true, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hd.le]
    push_cast; rfl
  · rw [if_neg hab]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hca : c = a
    · subst hca; simp [bell, hab]
    · simp [bell, hca]

/-- D8.13.1. `‖pre_k‖² = Tr (1/d_*)^{⊗k} π^λ = d_*^{-k} Tr π^λ`. -/
theorem star_pre_dotProduct_pre [NeZero d] (k : ℕ) (l : IrrepLabel (Equiv.Perm (Fin k))) :
    star (pre D d k l) ⬝ᵥ pre D d k l =
      ((d : ℂ))⁻¹ ^ k * (labelProj (copyPerm (Fin d) k) l).trace := by
  rw [pre, star_piR_dotProduct_piR_tensorVec d k _ (fun _ => ((d : ℂ))⁻¹)
    (sum_star_preVec_mul_preVec D d), tensorPow_diagonal]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul, trace_smul, smul_eq_mul]

/-- `Ω̃ ⊗ Bell` is a ground vector of the one-copy `H̃ ⊗ 1_{CR}`. -/
theorem Hx_mulVec_preVec : Hx D d *ᵥ preVec D d = (D.E₀ : ℂ) • preVec D d := by
  funext x
  have hg := congrFun D.ground (physPart x)
  simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hg ⊢
  have e1 : ∀ y, Hx D d x y * preVec D d y = if (x .C = y .C ∧ x .R = y .R) then
      D.H (physPart x) (physPart y) * D.Ω (physPart y) * bell d (x .C) (x .R) else 0 := by
    intro y
    simp only [Hx, preVec]
    split_ifs with h
    · simp only [h.1, h.2]; ring
    · ring
  rw [Finset.sum_congr rfl fun y _ => e1 y, ← Finset.sum_filter]
  calc _ = ∑ x' : SiteConfig n, D.H (physPart x) x' * D.Ω x' * bell d (x .C) (x .R) :=
        Finset.sum_nbij' (fun y => physPart y) (fun x' => (splitR d).symm (x .R, (x', x .C)))
          (fun _ _ => Finset.mem_univ _)
          (fun x' _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, rfl⟩)
          (fun y hy => by
            have h := (Finset.mem_filter.mp hy).2
            funext f
            cases f with
            | phys v => rfl
            | C => exact h.1
            | R => exact h.2)
          (fun _ _ => rfl) (fun _ _ => rfl)
    _ = _ := by rw [← Finset.sum_mul, hg, preVec]; ring

omit [Fintype σ] in
/-- `A^{(j)} φ^{⊗k} = c φ^{⊗k}` for an eigenvector `A φ = c φ`. -/
theorem siteOp_mulVec_tensorVec {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {k : ℕ} (j : Fin k)
    {A : Matrix Ω Ω ℂ} {φ : Ω → ℂ} {c : ℂ} (h : A *ᵥ φ = c • φ) :
    siteOp j A *ᵥ tensorVec k φ = c • tensorVec k φ := by
  funext x
  rw [siteOp_mulVec_apply]
  have e : ∀ y, tensorVec k φ (Function.update x j y) =
      φ y * ∏ i ∈ Finset.univ.erase j, φ (x i) := fun y => by
    rw [tensorVec, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j), Function.update_self]
    congr 1
    exact Finset.prod_congr rfl fun i hi => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  simp_rw [e, ← _root_.mul_assoc, ← Finset.sum_mul]
  have hj := congrFun h (x j)
  simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hj
  rw [hj, Pi.smul_apply, smul_eq_mul, tensorVec, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  ring

/-- D8.13.2. `\overline{H̃} (Ω̃ ⊗ Bell)^{⊗k} = Ẽ₀ (Ω̃ ⊗ Bell)^{⊗k}` for `k ≥ 1`. -/
theorem Hbar_mulVec_tensorVec {k : ℕ} (hk : 0 < k) :
    Hbar D d k *ᵥ tensorVec k (preVec D d) = (D.E₀ : ℂ) • tensorVec k (preVec D d) := by
  rw [Hbar, TensorPower.copyMean, smul_mulVec, sum_mulVec]
  simp_rw [siteOp_mulVec_tensorVec _ (Hx_mulVec_preVec D d)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ k,
    smul_smul, inv_mul_cancel₀ (by exact_mod_cast hk.ne'), one_smul]

/-- `H̃ ⊗ 1_{CR}` acts on the physical factors only. -/
theorem isSupportedOn_Hx : Entropy.IsSupportedOn (Hx D d) (physReg Finset.univ) := by
  refine ⟨fun x y ⟨f, hf, hxy⟩ => ?_, fun x y x' y' hx hy hxy hxy' => ?_⟩
  · cases f with
    | phys v => exact absurd (phys_mem_physReg v) hf
    | C => simp [Hx, hxy]
    | R => simp [Hx, hxy]
  · have e : ∀ z z' : SiteConfig (dims n d), (∀ f ∈ physReg Finset.univ, z f = z' f) →
        physPart z = physPart z' := fun z z' h => funext fun v => h _ (phys_mem_physReg v)
    simp only [Hx, e x x' hx, e y y' hy, hxy _ (C_not_mem_physReg _),
      hxy _ (R_not_mem_physReg _), hxy' _ (C_not_mem_physReg _), hxy' _ (R_not_mem_physReg _)]

/-- `Ω̃` on the physical factors. -/
noncomputable def physΩ : ((f : physReg (Finset.univ : Finset σ)) → Fin (dims n d f)) → ℂ :=
  fun y => D.Ω fun v => y ⟨.phys v, phys_mem_physReg v⟩

/-- `Bell_{CR}^{⊗k}`, a symmetric vector of the `CR` factors. -/
noncomputable def bellVec (k : ℕ) : Transport.Config (dims n d) k → ℂ :=
  tensorVec k fun s => bell d (s .C) (s .R)

theorem tensorVec_preVec_eq_fixFactor (k : ℕ) :
    tensorVec k (preVec D d) =
      Replicas.fixFactor (fun f => Fin (dims n d f)) k (physReg Finset.univ) (physΩ D d)
        (bellVec d k) := by
  funext x
  simp only [tensorVec, preVec, Replicas.fixFactor, bellVec, physΩ, Finset.prod_mul_distrib]
  rfl

omit [DecidableEq σ] in
theorem bellVec_congr {k : ℕ} (x y : Transport.Config (dims n d) k)
    (h : ∀ j, ∀ f, f ∉ physReg (Finset.univ : Finset σ) → x j f = y j f) :
    bellVec d k x = bellVec d k y := by
  simp only [bellVec, tensorVec, h _ _ (C_not_mem_physReg _), h _ _ (R_not_mem_physReg _)]

theorem tensorVec_mem_S {k : ℕ} (φ : SiteConfig (dims n d) → ℂ) :
    tensorVec k φ ∈ Replicas.S (fun f => Fin (dims n d f)) k := by
  rw [Replicas.S, Replicas.copyPerm, TensorPower.subsystemPerm_univ]
  exact tensorVec_mem_symmetricSubspace φ

/-- D8.13.3. `Bell^{⊗k}` is symmetric and lives on `CR`: its complementary labels agree,
`π^λ_C Bell^{⊗k} = π^λ_R Bell^{⊗k}` (Lemma 6.1 (2)). -/
theorem piC_bellVec {k : ℕ} (l : IrrepLabel (Equiv.Perm (Fin k))) :
    Replicas.π (fun f => Fin (dims n d f)) k {Site.C} l *ᵥ bellVec d k =
      Replicas.π (fun f => Fin (dims n d f)) k {Site.R} l *ᵥ bellVec d k := by
  have h1 : ∀ w : Transport.Config (dims n d) k → ℂ,
      Replicas.fixFactor (fun f => Fin (dims n d f)) k (physReg Finset.univ) (fun _ => 1) w =
        w := fun w => by
    funext x; simp [Replicas.fixFactor]
  have hS : bellVec d k ∈ Replicas.S (fun f => Fin (dims n d f)) k := tensorVec_mem_S d _
  have h2 := Replicas.π_fixFactor (fun f => Fin (dims n d f)) k (B := physReg Finset.univ)
    (Q := {Site.R}) (fun _ => 1) (bellVec_congr d) l
  rw [h1, h1] at h2
  rw [Replicas.step_6_4_9 _ k _ l hS, compl_C, h2]

/-- D8.13.3. `π^λ_C (Ω̃ ⊗ Bell)^{⊗k} = π^λ_R (Ω̃ ⊗ Bell)^{⊗k}`: on the symmetric vector both are
`Ω̃^{⊗k} ⊗ π^λ Bell^{⊗k}`. -/
theorem piC_tensorVec_preVec {k : ℕ} (l : IrrepLabel (Equiv.Perm (Fin k))) :
    piC d k l *ᵥ tensorVec k (preVec D d) = piR d k l *ᵥ tensorVec k (preVec D d) := by
  have hS := tensorVec_mem_S d (k := k) (preVec D d)
  have hC := Replicas.π_fixFactor (fun f => Fin (dims n d f)) k (B := physReg Finset.univ)
    (Q := {Site.R}) (physΩ D d) (bellVec_congr d) l
  have hR := Replicas.π_fixFactor (fun f => Fin (dims n d f)) k (B := physReg Finset.univ)
    (Q := {Site.C}) (physΩ D d) (bellVec_congr d) l
  rw [← tensorVec_preVec_eq_fixFactor] at hC hR
  rw [piC, piR, Replicas.step_6_4_9 _ k _ l hS, Replicas.step_6_4_9 _ k {Site.R} l hS, compl_C,
    compl_R, hC, hR, piC_bellVec]

/-- D8.13.4. A label projector of a subsystem contained in or disjoint from each part of a band
commutes with the band metric `A_{j,g}`. -/
theorem commute_bandA_π {K : ℕ} {St : Type v} {X : Finset σ} (Γ : Statuses σ K St X)
    [∀ v, NeZero (n v)] [NeZero d] {t : ℝ} (ht : 0 ≤ t) (k : ℕ) (s : St) (g : Fin K)
    {Q₀ : Finset (Site σ)} (hP : Q₀ ⊆ Γ.P s g ∨ Disjoint Q₀ (Γ.P s g))
    (hY : Q₀ ⊆ Γ.Yr s g ∨ Disjoint Q₀ (Γ.Yr s g)) (hF : Q₀ ⊆ Γ.F s g ∨ Disjoint Q₀ (Γ.F s g))
    (l : IrrepLabel (Equiv.Perm (Fin k))) :
    Commute (Γ.bandA n d t k s g) (Replicas.π (fun f => Fin (dims n d f)) k Q₀ l) := by
  set ι := fun f => Fin (dims n d f)
  have hX : Replicas.π ι k Q₀ l = labelObservable (Replicas.copyPerm ι k Q₀)
      fun l' => if l' = l then 1 else 0 := labelProj_eq_labelObservable _ l
  have hW : ∀ Q, (Q₀ ⊆ Q ∨ Disjoint Q₀ Q) → Commute (Replicas.π ι k Q₀ l) (Replicas.W ι t k Q) ∧
      Commute (Replicas.π ι k Q₀ l) (Replicas.W ι t k Q)⁻¹ := fun Q hQ => by
    rw [hX, Replicas.W_inv ι ht]
    exact ⟨Replicas.commute_labelObservable ι k hQ _ _,
      Replicas.commute_labelObservable ι k hQ _ _⟩
  have hA : Commute (Replicas.π ι k Q₀ l) (Replicas.A ι t k (Γ.P s g) (Γ.Yr s g) (Γ.F s g)) :=
    ((((hW _ hP).2.mul_right (hW _ hF).2).mul_right (hW _ hY).1).pow_right 2)
  have hPi : Commute (Replicas.π ι k Q₀ l) (Transport.Pi (dims n d) k) := by
    rw [hX]
    exact (Transport.commute_Pi_of_forall fun τ =>
      TensorPower.commute_copyPerm_labelObservable k Q₀ _ τ).symm
  exact ((hPi.mul_right hA).add_right ((Commute.one_right _).sub_right hPi)).symm

/-- `π^λ_R` commutes with the copy permutations, so `pre_k ∈ 𝒮_k`. -/
theorem pre_mem_S (k : ℕ) (l : IrrepLabel (Equiv.Perm (Fin k))) :
    pre D d k l ∈ Replicas.S (fun f => Fin (dims n d f)) k := by
  intro τ
  have hcomm : Commute (permOp (TensorPower.copyPerm (SiteConfig (dims n d)) k) τ)
      (piR d k l) := by
    rw [piR, Replicas.π, labelProj_eq_labelObservable]
    exact TensorPower.commute_copyPerm_labelObservable k _ _ τ
  change permOp (Replicas.copyPerm (fun f => Fin (dims n d f)) k Finset.univ) τ *ᵥ
    pre D d k l = _
  rw [Replicas.copyPerm, TensorPower.subsystemPerm_univ, pre, mulVec_mulVec, hcomm.eq,
    ← mulVec_mulVec]
  congr 1
  have := tensorVec_mem_S d (k := k) (preVec D d) τ
  rwa [Replicas.copyPerm, TensorPower.subsystemPerm_univ] at this

/-- `Tr π^λ ≤ dim (ℂ^q)^{⊗k} = q^k`. -/
theorem trace_labelProj_le {q k : ℕ} (l : IrrepLabel (Equiv.Perm (Fin k))) {m : ℕ}
    (hm : (labelProj (copyPerm (Fin q) k) l).trace = m) : m ≤ q ^ k := by
  have h2 : ∀ μ, ∃ m' : ℕ, (labelProj (copyPerm (Fin q) k) μ).trace = m' := fun μ =>
    ⟨_, trace_labelProj _ _⟩
  choose m' hm' using h2
  have h1 : ∑ μ, (m' μ : ℂ) = (q ^ k : ℕ) := by
    simp only [← hm']
    rw [← trace_sum, sum_labelProj, trace_one, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_fin]
  have h3 : ∑ μ, m' μ = q ^ k := by exact_mod_cast h1
  have h4 : m = m' l := by exact_mod_cast hm.symm.trans (hm' l)
  rw [h4, ← h3]
  exact Finset.single_le_sum (fun μ _ => Nat.zero_le (m' μ)) (Finset.mem_univ _)

/-- D8.13.1 (a). The `R`-marginal of `Bell^{⊗k}` is maximally mixed, so
`‖pre_k‖² = d_*^{-k} Tr π^λ = d_*^{-k} d_λ dim V_λ`: positive when `π^λ ≠ 0` (at most `d_*`
rows), and at most `1`. -/
theorem step_8_13_1 [NeZero d] (k : ℕ) (l : IrrepLabel (Equiv.Perm (Fin k)))
    (hπ : labelProj (copyPerm (Fin d) k) l ≠ 0) :
    pre D d k l ≠ 0 ∧ (star (pre D d k l) ⬝ᵥ pre D d k l).re ≤ 1 := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (labelProj (copyPerm (Fin d) k) l).trace = m :=
    ⟨_, trace_labelProj _ _⟩
  have hm0 : m ≠ 0 := fun h0 => hπ (((posSemidef_labelProj _ _).trace_eq_zero_iff).mp
    (by rw [hm, h0, Nat.cast_zero]))
  have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hnorm := star_pre_dotProduct_pre D d k l
  rw [hm] at hnorm
  refine ⟨fun h0 => ?_, ?_⟩
  · rw [h0, dotProduct_zero] at hnorm
    have h := (mul_eq_zero.mp hnorm.symm).resolve_left
      (pow_ne_zero _ (inv_ne_zero (by exact_mod_cast hdpos.ne')))
    exact hm0 (by exact_mod_cast h)
  · have e : ((d : ℂ))⁻¹ ^ k * (m : ℂ) = (((d : ℝ)⁻¹ ^ k * m : ℝ) : ℂ) := by push_cast; ring
    rw [hnorm, e, Complex.ofReal_re, inv_pow, inv_mul_le_iff₀ (pow_pos hdpos k), _root_.mul_one]
    exact_mod_cast trace_labelProj_le l hm

/-- D8.13.2 (b). `π^λ_R` acts on `R` only, so it commutes with every `H̃^{(i)}`; with
`H̃^{(i)} Ω̃^{(i)} = Ẽ₀ Ω̃^{(i)}`: `\overline{H̃} pre_k = Ẽ₀ pre_k` (`k ≥ 1`). -/
theorem step_8_13_2 {k : ℕ} (hk : 0 < k) (l : IrrepLabel (Equiv.Perm (Fin k))) :
    Hbar D d k *ᵥ pre D d k l = (D.E₀ : ℂ) • pre D d k l := by
  have hcomm : Commute (piR d k l) (Hbar D d k) := by
    rw [piR, Replicas.π, labelProj_eq_labelObservable]
    exact commute_labelObservable_of_forall_commute _ (fun τ =>
      Replicas.commute_permOp_copyMean (isSupportedOn_Hx D d)
        (Or.inr (Finset.disjoint_singleton_left.mpr (R_not_mem_physReg _))) τ) _
  rw [pre, mulVec_mulVec, ← hcomm.eq, ← mulVec_mulVec, Hbar_mulVec_tensorVec D d hk, mulVec_smul]

/-- D8.13.3 (c). `Bell^{⊗k}_{CR}` is symmetric: its `C` label equals its `R` label, and
`π^λ_R` commutes with the `C` label, so `pre_k` has label `λ` on `C` and on `R`. -/
theorem step_8_13_3 {k : ℕ} (l : IrrepLabel (Equiv.Perm (Fin k))) :
    piC d k l *ᵥ pre D d k l = pre D d k l ∧ piR d k l *ᵥ pre D d k l = pre D d k l := by
  have hCR : Commute (piC d k l) (piR (n := n) d k l) :=
    Replicas.step_6_4_8 _ k (Or.inr (by simp)) l l
  refine ⟨?_, by rw [pre, mulVec_mulVec, piR, Replicas.π, labelProj_mul_self]⟩
  rw [pre, mulVec_mulVec, hCR.eq, ← mulVec_mulVec, piC_tensorVec_preVec, mulVec_mulVec, piR,
    Replicas.π, labelProj_mul_self]

/-- D8.13.4 (d). `C ⊆ P_{j,g}`, `R ⊆ F_{j,g}`, and `Y_{j,g}` is disjoint from both, so
`π^λ_C`, `π^λ_R` commute with every `A_{j,g}`, hence with every `A_j` and every root `𝓜`. -/
theorem step_8_13_4 [∀ v, NeZero (n v)] [NeZero d] {K : ℕ} {St : Type v} {X : Finset σ}
    (Γ : Statuses σ K St X) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) (l : IrrepLabel (Equiv.Perm (Fin k))) :
    (∀ s g, Commute (Γ.bandA n d t k s g) (piC d k l) ∧
      Commute (Γ.bandA n d t k s g) (piR d k l)) ∧
    ∀ T : Transport.MeanTree St, Commute (Γ.root n d T t k) (piC d k l) ∧
      Commute (Γ.root n d T t k) (piR d k l) := by
  have hband : ∀ s g, Commute (Γ.bandA n d t k s g) (piC d k l) ∧
      Commute (Γ.bandA n d t k s g) (piR d k l) := fun s g =>
    ⟨commute_bandA_π d Γ ht k s g
        (Or.inl (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)))
        (Or.inr (Finset.disjoint_singleton_left.mpr (C_not_mem_physReg _)))
        (Or.inr (Finset.disjoint_singleton_left.mpr (by simp [Statuses.F, physReg]))) _,
      commute_bandA_π d Γ ht k s g
        (Or.inr (Finset.disjoint_singleton_left.mpr (by simp [Statuses.P, physReg])))
        (Or.inr (Finset.disjoint_singleton_left.mpr (R_not_mem_physReg _)))
        (Or.inl (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))) _⟩
  refine ⟨hband, fun T => ⟨?_, ?_⟩⟩
  · exact (commute_eval_of_commute (fun s => Commute.list_prod_right _ _ fun A hA => by
      obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hA
      exact (hband s g).1.symm) T).symm
  · exact (commute_eval_of_commute (fun s => Commute.list_prod_right _ _ fun A hA => by
      obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hA
      exact (hband s g).2.symm) T).symm

/-- D8.13. (a) `pre_k ≠ 0`, `‖pre_k‖ ≤ 1`. (b) `\overline{H̃} pre_k = Ẽ₀ pre_k`. (c) `pre_k` has
label `λ_k` on `C` and on `R`. (d) Each `W_Q` of D8.6 preserves these labels and `𝒮_k`; hence so
does every `A_{j,g}`, `A_j`, `𝓜^r`. -/
theorem step_8_13 (h11 : Step_8_11.{u}) : Step_8_13.{u, v} := by
  intro σ _ _ n _ D X E l hl k
  obtain ⟨c, N, hc, ε, -, hq⟩ := hl
  -- D8.13.1 (a): `λ_k` occurs in `ρ_R^{⊗k}` (`q_k > 0`, D8.12), so `π^{λ_k} ≠ 0`
  have hπ : labelProj (copyPerm (Fin E.d) k) (l k) ≠ 0 := by
    intro h0
    have h := (hq k).1
    rw [q_eq_re_trace h11 E k (l k), h0, Matrix.mul_zero, trace_zero, Complex.zero_re] at h
    exact absurd h (not_le.mpr (mul_pos hc (Real.rpow_pos_of_pos (by positivity) _)))
  exact ⟨pre_mem_S D E.d k (l k), (step_8_13_1 D E.d k (l k) hπ).1,
    (step_8_13_1 D E.d k (l k) hπ).2, fun hk => step_8_13_2 D E.d hk (l k),
    (step_8_13_3 D E.d (l k)).1, (step_8_13_3 D E.d (l k)).2,
    fun Γ t ht => step_8_13_4 E.d Γ ht k (l k)⟩

end PrevectorSec

end AreaLaw.Comparators
