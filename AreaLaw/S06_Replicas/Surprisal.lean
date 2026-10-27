import AreaLaw.S06_Replicas.Setup
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# §6 Lemma 6.1 (5): the surprisal bounds
-/

namespace AreaLaw.Replicas

open Matrix MonoidAlgebra PermutationRepresentation
open scoped ComplexOrder MatrixOrder

section Spectral

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- D6.4 (5). The surprisal `L_ρ = -log ρ` on `supp ρ`; it is `0` on `ker ρ`, since
`Real.log 0 = 0`. -/
noncomputable def L (ρ : Matrix X X ℂ) : Matrix X X ℂ := cfc (fun u => -Real.log u) ρ

/-- D6.4 (5). The support projector of `ρ`: `1` on `supp ρ`, `0` on `ker ρ`. -/
noncomputable def suppProj (ρ : Matrix X X ℂ) : Matrix X X ℂ :=
  cfc (fun u : ℝ => if u = 0 then 0 else 1) ρ

/-- The quadratic form of `f(ρ)` in the eigenbasis of `ρ`. -/
theorem dotProduct_cfc_mulVec {ρ : Matrix X X ℂ} (hρ : ρ.IsHermitian) (f : ℝ → ℝ)
    (y : X → ℂ) :
    star y ⬝ᵥ (cfc f ρ *ᵥ y) = ∑ i, (f (hρ.eigenvalues i) : ℂ) *
      (star ((star (hρ.eigenvectorUnitary : Matrix X X ℂ) *ᵥ y) i) *
        (star (hρ.eigenvectorUnitary : Matrix X X ℂ) *ᵥ y) i) := by
  have hV : star y ᵥ* (hρ.eigenvectorUnitary : Matrix X X ℂ) =
      star (star (hρ.eigenvectorUnitary : Matrix X X ℂ) *ᵥ y) := by
    rw [star_mulVec, star_eq_conjTranspose, conjTranspose_conjTranspose]
  rw [hρ.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, ← mulVec_mulVec, ← mulVec_mulVec,
    dotProduct_mulVec, hV]
  simp only [dotProduct, mulVec_diagonal, Function.comp_apply, Pi.star_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_left_comm]; rfl

/-- In the eigenbasis of `A`, an eigenvector of `A` has no component off its eigenvalue. -/
theorem star_eigenvectorUnitary_mulVec_eq_zero {A : Matrix X X ℂ} (hA : A.IsHermitian)
    {w : X → ℂ} {c : ℝ} (hw : A *ᵥ w = (c : ℂ) • w) {i : X} (hi : hA.eigenvalues i ≠ c) :
    (star (hA.eigenvectorUnitary : Matrix X X ℂ) *ᵥ w) i = 0 := by
  set V := (hA.eigenvectorUnitary : Matrix X X ℂ)
  have hspec : star V * A = diagonal (fun i => (hA.eigenvalues i : ℂ)) * star V := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, ← mul_assoc, ← mul_assoc, Unitary.coe_star_mul_self,
      one_mul]
    rfl
  have h := congrFun (congrArg (star V *ᵥ ·) hw) i
  rw [mulVec_mulVec, hspec, ← mulVec_mulVec, mulVec_diagonal, mulVec_smul, Pi.smul_apply,
    smul_eq_mul] at h
  have : ((hA.eigenvalues i : ℂ) - c) * (star V *ᵥ w) i = 0 := by rw [sub_mul, h, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (mod_cast hi))

omit [DecidableEq X] in
/-- An eigenvalue `u` with `d` linearly independent eigenvectors satisfies `d u ≤ Tr ρ`. -/
theorem card_mul_le_trace {ρ : Matrix X X ℂ} (hρ : ρ.PosSemidef) {d : ℕ} {u : ℝ}
    (z : Fin d → X → ℂ) (hz : LinearIndependent ℂ z) (heig : ∀ j, ρ *ᵥ z j = (u : ℂ) • z j) :
    d * u ≤ (trace ρ).re := by
  classical
  have htr : (trace ρ).re = ∑ i, hρ.1.eigenvalues i := by
    rw [hρ.1.trace_eq_sum_eigenvalues]; simp
  rcases le_or_gt u 0 with hu | hu
  · rw [htr]
    exact (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg d) hu).trans
      (Finset.sum_nonneg fun i _ => hρ.eigenvalues_nonneg i)
  set ev := hρ.1.eigenvalues
  set V := (hρ.1.eigenvectorUnitary : Matrix X X ℂ)
  set z' : Fin d → X → ℂ := fun j => star V *ᵥ z j
  have hVV : V * star V = 1 := Unitary.coe_mul_star_self _
  have hz' : ∀ j i, ev i ≠ u → z' j i = 0 := fun j i hi =>
    star_eigenvectorUnitary_mulVec_eq_zero hρ.1 (heig j) hi
  set S := {i // ev i = u}
  have hr : LinearIndependent ℂ (fun j (i : S) => z' j i) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have h1 : ∑ j, c j • z' j = 0 := by
      funext i
      by_cases hi : ev i = u
      · simpa [Finset.sum_apply] using congrFun hc ⟨i, hi⟩
      · simp [Finset.sum_apply, hz' _ i hi]
    have h2 : ∑ j, c j • z j = 0 := by
      have : ∀ j, z j = V *ᵥ z' j := fun j => by simp [z', mulVec_mulVec, hVV]
      simp_rw [this, ← mulVec_smul, ← mulVec_sum, h1, mulVec_zero]
    exact Fintype.linearIndependent_iff.mp hz c h2
  have hcard : d ≤ (Finset.univ.filter fun i => ev i = u).card := by
    simpa [Module.finrank_fintype_fun_eq_card, Fintype.card_subtype, S] using
      hr.fintype_card_le_finrank
  rw [htr]
  calc (d : ℝ) * u ≤ (Finset.univ.filter fun i => ev i = u).card * u := by gcongr
    _ = ∑ i ∈ Finset.univ.filter (fun i => ev i = u), ev i := by
      rw [Finset.sum_congr rfl fun i hi => (Finset.mem_filter.mp hi).2]; simp
    _ ≤ ∑ i, ev i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun i _ _ => hρ.eigenvalues_nonneg i

/-- An eigenvector of `A` with eigenvalue `c` is an eigenvector of `f(A)` with eigenvalue
`f(c)`. -/
theorem cfc_mulVec_of_mulVec_eq {A : Matrix X X ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ)
    {w : X → ℂ} {c : ℝ} (hw : A *ᵥ w = (c : ℂ) • w) : cfc f A *ᵥ w = (f c : ℂ) • w := by
  set V := (hA.eigenvectorUnitary : Matrix X X ℂ)
  have hVV : V * star V = 1 := Unitary.coe_mul_star_self _
  have hD : diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues) *ᵥ (star V *ᵥ w) =
      (f c : ℂ) • (star V *ᵥ w) := by
    funext i
    rw [mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    by_cases hi : hA.eigenvalues i = c
    · simp [hi]
    · simp [V, star_eigenvectorUnitary_mulVec_eq_zero hA hw hi]
  rw [hA.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, ← mulVec_mulVec,
    ← mulVec_mulVec, hD, mulVec_smul, mulVec_mulVec, hVV, one_mulVec]

/-- The trace in the eigenbasis of a Hermitian matrix. -/
theorem trace_eq_sum_dotProduct {ρ : Matrix X X ℂ} (hρ : ρ.IsHermitian) (A : Matrix X X ℂ) :
    trace A = ∑ i, star ⇑(hρ.eigenvectorBasis i) ⬝ᵥ (A *ᵥ ⇑(hρ.eigenvectorBasis i)) := by
  set V := (hρ.eigenvectorUnitary : Matrix X X ℂ)
  have hVV : V * star V = 1 := Unitary.coe_mul_star_self _
  rw [show trace A = trace (star V * (A * V)) by rw [trace_mul_comm, mul_assoc, hVV, mul_one]]
  simp only [trace, diag, Matrix.mul_apply, dotProduct, mulVec, Matrix.star_apply, V,
    IsHermitian.eigenvectorUnitary_apply, Pi.star_apply]

end Spectral

section Surprisal

variable {I : Type*} [DecidableEq I] (ι : I → Type*) (k : ℕ)
variable [Fintype I] [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]

/-- D6.4.15 (multiplicity). An eigenvector `w` of an invariant `ρ` with eigenvalue `u` in the
block `λ` gives `d_λ` linearly independent eigenvectors (the images of the matrix units of
`λ`), so `d_λ u ≤ Tr ρ`. -/
theorem dim_mul_le_trace {ρ : Matrix (Config ι k) (Config ι k) ℂ} (hρ : ρ.PosSemidef)
    (hinv : ∀ σ, Commute (U ι k Finset.univ σ) ρ) (l : IrrepLabel (Equiv.Perm (Fin k)))
    {w : Config ι k → ℂ} (hw : w ≠ 0) {u : ℝ} (hu : ρ *ᵥ w = (u : ℂ) • w)
    (hπ : π ι k Finset.univ l *ᵥ w = w) : l.dim * u ≤ (trace ρ).re := by
  set φ := copyPerm ι k Finset.univ
  set e : Fin l.dim → Fin l.dim → Matrix (Config ι k) (Config ι k) ℂ :=
    fun i j => groupAlgebraRep φ (IrrepLabel.matrixUnit l i j)
  have hcomm : ∀ i j, Commute (e i j) ρ := fun i j =>
    commute_groupAlgebraRep_of_forall_commute φ hinv _
  have hmul : ∀ i j j' m, e i j * e j' m = if j = j' then e i m else 0 := by
    intro i j j' m
    simp only [e, ← map_mul, IrrepLabel.matrixUnit_mul_matrixUnit]
    split_ifs <;> simp
  have hsum : π ι k Finset.univ l = ∑ i, e i i := by
    simp only [e, ← map_sum, IrrepLabel.sum_matrixUnit_diag]; rfl
  have key : ∀ M v, Commute M ρ → ρ *ᵥ (M *ᵥ v) = M *ᵥ (ρ *ᵥ v) := fun M v h => by
    rw [mulVec_mulVec, mulVec_mulVec, h.eq]
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, e i₀ i₀ *ᵥ w ≠ 0 := by
    contrapose! hw
    rw [← hπ, hsum, sum_mulVec]
    exact Finset.sum_eq_zero fun i _ => hw i
  set w₀ := e i₀ i₀ *ᵥ w
  set z : Fin l.dim → Config ι k → ℂ := fun j => e j i₀ *ᵥ w₀
  have hez : ∀ j j', e i₀ j' *ᵥ z j = if j' = j then w₀ else 0 := by
    intro j j'
    simp only [z, w₀, mulVec_mulVec, hmul]
    rw [if_pos trivial, hmul]; split_ifs <;> simp
  refine card_mul_le_trace hρ z ?_ fun j => ?_
  · rw [Fintype.linearIndependent_iff]
    intro c hc j'
    have h := congrArg (e i₀ j' *ᵥ ·) hc
    simp only [mulVec_sum, mulVec_smul, hez, smul_ite, smul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, mulVec_zero] at h
    exact (smul_eq_zero.mp h).resolve_right hi₀
  · simp only [z, w₀]
    rw [key _ _ (hcomm j i₀), key _ _ (hcomm i₀ i₀), hu, mulVec_smul, mulVec_smul]

/-- D6.4.15 (one block). On the block `λ`, `L_ρ - (log d_λ) 1_{supp ρ} ≥ 0`. -/
theorem dotProduct_L_sub_log_dim_nonneg {ρ : Matrix (Config ι k) (Config ι k) ℂ}
    (hρ : ρ.PosSemidef) (htr : (trace ρ).re ≤ 1) (hinv : ∀ σ, Commute (U ι k Finset.univ σ) ρ)
    (l : IrrepLabel (Equiv.Perm (Fin k))) (x : Config ι k → ℂ) :
    0 ≤ star (π ι k Finset.univ l *ᵥ x) ⬝ᵥ
      ((L ρ - (Real.log l.dim : ℂ) • suppProj ρ) *ᵥ (π ι k Finset.univ l *ᵥ x)) := by
  set Pl := π ι k Finset.univ l
  have hPl : Plᴴ = Pl := isHermitian_labelProj _ l
  have hPlρ : Commute Pl ρ := commute_labelProj_of_forall_commute _ hinv l
  set b := hρ.1.eigenvectorBasis
  set V := (hρ.1.eigenvectorUnitary : Matrix (Config ι k) (Config ι k) ℂ)
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, L, suppProj,
    dotProduct_cfc_mulVec hρ.1, dotProduct_cfc_mulVec hρ.1, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_nonneg fun i _ => ?_
  set zi := (star V *ᵥ (Pl *ᵥ x)) i
  have hcoord : ∀ v, (star V *ᵥ v) i = star ⇑(b i) ⬝ᵥ v := fun v => by
    simp only [mulVec, dotProduct, Matrix.star_apply, V, IsHermitian.eigenvectorUnitary_apply,
      Pi.star_apply, b]
  have hzi : zi = star (Pl *ᵥ ⇑(b i)) ⬝ᵥ x := by
    rw [show zi = _ from hcoord _, dotProduct_mulVec, star_mulVec, hPl]
  set ev := hρ.1.eigenvalues
  by_cases hz : zi = 0
  · simp [hz]
  by_cases h0 : ev i = 0
  · simp [h0]
  have hpos : 0 < ev i := lt_of_le_of_ne (hρ.eigenvalues_nonneg i) (Ne.symm h0)
  have hd : l.dim * ev i ≤ 1 := by
    refine le_trans (dim_mul_le_trace ι k hρ hinv l (w := Pl *ᵥ ⇑(b i)) ?_ ?_ ?_) htr
    · intro h; exact hz (by rw [hzi, h, star_zero, zero_dotProduct])
    · rw [mulVec_mulVec, ← hPlρ.eq, ← mulVec_mulVec, hρ.1.mulVec_eigenvectorBasis,
        ← Complex.coe_smul, mulVec_smul]
    · rw [mulVec_mulVec, show Pl * Pl = Pl from labelProj_mul_self _ l]
  have hlog : Real.log l.dim ≤ -Real.log (ev i) := by
    have := Real.log_le_log (mul_pos (mod_cast l.dim_pos) hpos) hd
    rw [Real.log_mul (mod_cast l.dim_pos.ne') hpos.ne', Real.log_one] at this
    linarith
  have : ((-Real.log (ev i) : ℝ) : ℂ) * (star zi * zi) -
      (Real.log l.dim : ℂ) * (((if ev i = 0 then 0 else 1 : ℝ)) * (star zi * zi)) =
      ((-Real.log (ev i) - Real.log l.dim : ℝ) : ℂ) * (star zi * zi) := by
    rw [if_neg h0]; push_cast; ring
  rw [this]
  exact mul_nonneg (Complex.zero_le_real.mpr (by linarith)) (star_mul_self_nonneg _)

/-- D6.4.15. For a permutation-invariant density `ρ` on `𝒱^{⊗k}`: `[F, ρ] = 0`, `F ≥ 0`, and
`F ≤ L_ρ` on the support of `ρ`. -/
theorem step_6_4_15 {ρ : Matrix (Config ι k) (Config ι k) ℂ} (hρ : ρ.PosSemidef)
    (htr : (trace ρ).re ≤ 1) (hinv : ∀ σ, Commute (U ι k Finset.univ σ) ρ) :
    Commute (F ι k Finset.univ) ρ ∧ (F ι k Finset.univ).PosSemidef ∧
      suppProj ρ * F ι k Finset.univ * suppProj ρ ≤ L ρ := by
  set P := suppProj ρ
  set c : IrrepLabel (Equiv.Perm (Fin k)) → ℂ := fun l => (Real.log l.dim : ℂ)
  have hρπ : ∀ l, Commute ρ (π ι k Finset.univ l) := fun l =>
    (commute_labelProj_of_forall_commute _ hinv l).symm
  have hππ : ∀ l, π ι k Finset.univ l * π ι k Finset.univ l = π ι k Finset.univ l :=
    fun l => labelProj_mul_self _ l
  have hπL : ∀ l, π ι k Finset.univ l * L ρ = L ρ * π ι k Finset.univ l := fun l =>
    ((hρπ l).cfc_real _).eq.symm
  have hπP : ∀ l, π ι k Finset.univ l * P = P * π ι k Finset.univ l := fun l =>
    ((hρπ l).cfc_real _).eq.symm
  have hl : ∀ l, (π ι k Finset.univ l)ᴴ = π ι k Finset.univ l := fun l =>
    isHermitian_labelProj _ l
  have hsum : ∑ l, π ι k Finset.univ l = 1 := sum_labelProj _
  have hPP : P * P = P := by
    simp only [P, suppProj, hρ.1.cfc_eq, IsHermitian.cfc, ← map_mul, diagonal_mul_diagonal]
    congr 3; funext i; simp only [Function.comp_apply]; split_ifs <;> simp
  have hF : F ι k Finset.univ = ∑ l, c l • π ι k Finset.univ l := rfl
  -- D6.4.15: `L_ρ - P F P = ∑_λ π^λ (L_ρ - (log d_λ) P) π^λ`, as `ρ`, hence `L_ρ` and `P`,
  -- commute with every `π^λ`.
  have hdec : L ρ - P * F ι k Finset.univ * P =
      ∑ l, π ι k Finset.univ l * (L ρ - c l • P) * π ι k Finset.univ l := by
    have h1 : ∀ l, π ι k Finset.univ l * (L ρ - c l • P) * π ι k Finset.univ l =
        L ρ * π ι k Finset.univ l - c l • (P * π ι k Finset.univ l) := fun l => by
      rw [mul_sub, sub_mul, hπL, mul_assoc, hππ, mul_smul_comm, smul_mul_assoc, hπP, mul_assoc,
        hππ]
    have h2 : P * F ι k Finset.univ * P = ∑ l, c l • (P * π ι k Finset.univ l) := by
      rw [hF, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [mul_smul_comm, smul_mul_assoc, mul_assoc, hπP, ← mul_assoc, hPP]
    rw [Finset.sum_congr rfl fun l _ => h1 l, Finset.sum_sub_distrib, ← Finset.mul_sum,
      hsum, mul_one, h2]
  rw [Matrix.le_iff, hdec]
  refine ⟨commute_labelObservable_of_forall_commute _ hinv _, posSemidef_F ι k _, ?_⟩
  refine Finset.sum_induction _ PosSemidef (fun _ _ ha hb => ha.add hb) PosSemidef.zero
    fun l _ => posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun x => ?_⟩
  · have hP : P.IsHermitian := cfc_predicate _ ρ
    have hL : (L ρ).IsHermitian := cfc_predicate _ ρ
    rw [IsHermitian, conjTranspose_mul, conjTranspose_mul, hl, conjTranspose_sub,
      conjTranspose_smul, hP.eq, hL.eq, show star (c l) = c l from Complex.conj_ofReal _,
      mul_assoc]
  · have hx : star x ᵥ* π ι k Finset.univ l = star (π ι k Finset.univ l *ᵥ x) := by
      rw [star_mulVec, hl]
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, hx]
    exact dotProduct_L_sub_log_dim_nonneg ι k hρ htr hinv l x

/-- D6.4.16 (blocks). For `0 ≤ b ≤ 1`, the eigenvalue `u` of `ρ` in the block `λ` contributes
`d_λ u (u d_λ)^{-b} = (u d_λ)^{1-b} ≤ 1` per copy of `[λ]`, so
`Tr ρ e^{b(L_ρ - F)} ≤ ∑_λ dim V_λ`, where `dim V_λ = Tr π^λ / d_λ` is the multiplicity of
`[λ]` in `𝒱^{⊗k}`. -/
theorem trace_mul_exp_le_sum_dim {ρ : Matrix (Config ι k) (Config ι k) ℂ} (hρ : ρ.PosSemidef)
    (htr : (trace ρ).re ≤ 1) (hinv : ∀ σ, Commute (U ι k Finset.univ σ) ρ) {b : ℝ}
    (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    (trace (ρ * cfc Real.exp (b • (L ρ - F ι k Finset.univ)))).re ≤
      ∑ l, (trace (π ι k Finset.univ l)).re / l.dim := by
  set G := cfc Real.exp (b • (L ρ - F ι k Finset.univ))
  set ev := hρ.1.eigenvalues
  set bv : Config ι k → Config ι k → ℂ := fun i => ⇑(hρ.1.eigenvectorBasis i)
  set a : Config ι k → IrrepLabel (Equiv.Perm (Fin k)) → ℝ := fun i l =>
    ev i * Real.exp (b * (-Real.log (ev i) - Real.log l.dim))
  set s : Config ι k → IrrepLabel (Equiv.Perm (Fin k)) → ℂ := fun i l =>
    star (bv i) ⬝ᵥ (π ι k Finset.univ l *ᵥ bv i)
  have hL : (L ρ).IsHermitian := cfc_predicate _ ρ
  have hM : (b • (L ρ - F ι k Finset.univ)).IsHermitian :=
    (hL.sub (isHermitian_F ι k _)).smul (IsSelfAdjoint.all b)
  have hπρ : ∀ l, Commute (π ι k Finset.univ l) ρ := fun l =>
    commute_labelProj_of_forall_commute _ hinv l
  have hππ : ∀ l, π ι k Finset.univ l * π ι k Finset.univ l = π ι k Finset.univ l :=
    fun l => labelProj_mul_self _ l
  have hl : ∀ l, (π ι k Finset.univ l)ᴴ = π ι k Finset.univ l := fun l =>
    isHermitian_labelProj _ l
  have hsum : ∑ l, π ι k Finset.univ l = 1 := sum_labelProj _
  -- D6.4.16: `π^λ b_i` is an eigenvector of `ρ e^{b(L_ρ - F)}` with eigenvalue
  -- `u_i e^{b(-log u_i - log d_λ)}`.
  have heig : ∀ i l, (ρ * G) *ᵥ (π ι k Finset.univ l *ᵥ bv i) =
      (a i l : ℂ) • (π ι k Finset.univ l *ᵥ bv i) := by
    intro i l
    set w := π ι k Finset.univ l *ᵥ bv i
    have hwρ : ρ *ᵥ w = (ev i : ℂ) • w := by
      rw [mulVec_mulVec, ← (hπρ l).eq, ← mulVec_mulVec, hρ.1.mulVec_eigenvectorBasis,
        ← Complex.coe_smul, mulVec_smul]
    have hwF : F ι k Finset.univ *ᵥ w = (Real.log l.dim : ℂ) • w := by
      rw [mulVec_mulVec, show F ι k Finset.univ * π ι k Finset.univ l = _ from
        labelObservable_mul_labelProj _ _ l, smul_mulVec]
      rfl
    have hwL : L ρ *ᵥ w = ((-Real.log (ev i) : ℝ) : ℂ) • w := cfc_mulVec_of_mulVec_eq hρ.1 _ hwρ
    have hwM : (b • (L ρ - F ι k Finset.univ)) *ᵥ w =
        ((b * (-Real.log (ev i) - Real.log l.dim) : ℝ) : ℂ) • w := by
      funext j
      simp only [smul_mulVec, sub_mulVec, hwL, hwF, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
        Complex.real_smul]
      push_cast; ring
    rw [← mulVec_mulVec, cfc_mulVec_of_mulVec_eq hM _ hwM, mulVec_smul, hwρ, smul_smul]
    congr 1; simp only [a]; push_cast; ring
  have hs : ∀ i l, s i l = star (π ι k Finset.univ l *ᵥ bv i) ⬝ᵥ (π ι k Finset.univ l *ᵥ bv i) :=
    fun i l => by
      simp only [s]
      conv_lhs => rw [← hππ l]
      rw [← mulVec_mulVec, dotProduct_mulVec,
        show star (bv i) ᵥ* π ι k Finset.univ l = star (π ι k Finset.univ l *ᵥ bv i) by
          rw [star_mulVec, hl]]
  have hs0 : ∀ i l, 0 ≤ s i l := fun i l => (hs i l).symm ▸ dotProduct_star_self_nonneg _
  -- D6.4.16: each contribution is at most `1/d_λ` times the weight of `b_i` in the block `λ`.
  have hterm : ∀ i l, a i l * (s i l).re ≤ (s i l).re / l.dim := by
    intro i l
    have hsre : 0 ≤ (s i l).re := (Complex.nonneg_iff.mp (hs0 i l)).1
    by_cases hw : π ι k Finset.univ l *ᵥ bv i = 0
    · simp [hs i l, hw]
    have hd : (0 : ℝ) < l.dim := mod_cast l.dim_pos
    rw [div_eq_inv_mul]
    refine mul_le_mul_of_nonneg_right ?_ hsre
    by_cases h0 : ev i = 0
    · simp [a, h0, hd.le]
    have hpos : 0 < ev i := lt_of_le_of_ne (hρ.eigenvalues_nonneg i) (Ne.symm h0)
    have hdu : l.dim * ev i ≤ 1 := by
      refine le_trans (dim_mul_le_trace ι k hρ hinv l hw ?_ ?_) htr
      · rw [mulVec_mulVec, ← (hπρ l).eq, ← mulVec_mulVec, hρ.1.mulVec_eigenvectorBasis,
          ← Complex.coe_smul, mulVec_smul]
      · rw [mulVec_mulVec, hππ]
    have hlog : Real.log l.dim + Real.log (ev i) ≤ 0 := by
      rw [← Real.log_mul hd.ne' hpos.ne']
      exact Real.log_nonpos (by positivity) hdu
    simp only [a]
    rw [← Real.exp_log hpos, ← Real.exp_add, Real.exp_log hpos]
    calc _ ≤ Real.exp (-Real.log l.dim) := Real.exp_le_exp.mpr (by nlinarith [hb.1, hb.2])
      _ = _ := by rw [Real.exp_neg, Real.exp_log hd]
  -- D6.4.16: sum over the eigenbasis of `ρ` and the blocks.
  have htrG : trace (ρ * G) = ∑ i, ∑ l, (a i l : ℂ) * s i l := by
    rw [trace_eq_sum_dotProduct hρ.1]
    refine Finset.sum_congr rfl fun i _ => ?_
    change star (bv i) ⬝ᵥ ((ρ * G) *ᵥ bv i) = _
    rw [show (ρ * G) *ᵥ bv i = ∑ l, (ρ * G) *ᵥ (π ι k Finset.univ l *ᵥ bv i) by
      rw [← mulVec_sum, ← sum_mulVec, hsum, one_mulVec], dotProduct_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [heig, dotProduct_smul, smul_eq_mul]
  have htrπ : ∀ l, trace (π ι k Finset.univ l) = ∑ i, s i l := fun l =>
    trace_eq_sum_dotProduct hρ.1 _
  rw [htrG]
  simp only [htrπ, Complex.re_sum, Finset.sum_div]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun i _ =>
    (Complex.re_ofReal_mul _ _).symm ▸ hterm i l

/-! ### Counting copies of the Specht modules -/

/-- Two words with the same letter counts differ by a permutation of the positions. -/
theorem exists_perm_of_card_fiber_eq {Z : Type*} [DecidableEq Z] (p p' : Fin k → Z)
    (h : ∀ z, Fintype.card {j // p j = z} = Fintype.card {j // p' j = z}) :
    ∃ τ : Equiv.Perm (Fin k), ∀ j, p' j = p (τ j) := by
  refine ⟨(Equiv.sigmaFiberEquiv p').symm.trans ((Equiv.sigmaCongrRight fun z =>
    (Fintype.equivOfCardEq (h z)).symm).trans (Equiv.sigmaFiberEquiv p)), fun j => ?_⟩
  simp only [Equiv.trans_apply, Equiv.sigmaCongrRight_apply, Equiv.sigmaFiberEquiv_apply]
  exact ((Fintype.equivOfCardEq (h (p' j))).symm ⟨j, rfl⟩).2.symm

/-- The commutant of the `S_k` action on `𝒱^{⊗k}`. -/
noncomputable def commutant : Submodule ℂ (Matrix (Config ι k) (Config ι k) ℂ) where
  carrier := {T | ∀ σ, Commute (U ι k Finset.univ σ) T}
  add_mem' ha hb σ := (ha σ).add_right (hb σ)
  zero_mem' _ := Commute.zero_right _
  smul_mem' c _ ha σ := (ha σ).smul_right c

/-- Elements of the commutant are invariant under simultaneous permutation of the copies. -/
theorem commutant_apply_perm {T : Matrix (Config ι k) (Config ι k) ℂ}
    (hT : T ∈ commutant ι k) (σ : Equiv.Perm (Fin k)) (x y : Config ι k) :
    T (fun j => x (σ j)) (fun j => y (σ j)) = T x y := by
  have h := (hT σ⁻¹).eq
  simp only [U, permOp_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv] at h
  have h' := congrFun (congrFun h (copyPerm ι k Finset.univ σ⁻¹ x)) y
  simp only [submatrix_apply, id, Equiv.Perm.inv_def, Equiv.symm_symm,
    Equiv.symm_apply_apply] at h'
  convert h'.symm using 2 <;> ext j f <;> simp

/-- The commutant has dimension at most the number of `S_k`-orbits on pairs of
configurations, which is at most `(k+1)^{q²}`, `q = dim 𝒱`. -/
theorem finrank_commutant_le :
    Module.finrank ℂ (commutant ι k) ≤ (k + 1) ^ (Fintype.card ((f : I) → ι f) ^ 2) := by
  classical
  set Y := (f : I) → ι f
  set Z := Y × Y → Fin (k + 1)
  let cnt : Config ι k × Config ι k → Z := fun p z =>
    ⟨Fintype.card {j // (p.1 j, p.2 j) = z}, Nat.lt_succ_of_le
      ((Fintype.card_subtype_le _).trans (Fintype.card_fin k).le)⟩
  let Λ : commutant ι k →ₗ[ℂ] (Z → ℂ) :=
    { toFun := fun T c => if h : ∃ p, cnt p = c then (T : Matrix _ _ ℂ) h.choose.1 h.choose.2
        else 0
      map_add' := fun T T' => by
        funext c
        simp only [Pi.add_apply, Submodule.coe_add, Matrix.add_apply]
        split_ifs <;> simp
      map_smul' := fun a T => by
        funext c
        simp only [Pi.smul_apply, Submodule.coe_smul, Matrix.smul_apply, RingHom.id_apply]
        split_ifs <;> simp }
  have hΛ : Function.Injective Λ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro T hT
    ext x y
    have hc : ∃ p, cnt p = cnt (x, y) := ⟨_, rfl⟩
    have h0 := congrFun hT (cnt (x, y))
    simp only [Λ, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hc, Pi.zero_apply] at h0
    obtain ⟨τ, hτ⟩ := exists_perm_of_card_fiber_eq k (fun j => (hc.choose.1 j, hc.choose.2 j))
      (fun j => (x j, y j)) fun z => congrArg Fin.val (congrFun hc.choose_spec z)
    have hx : x = fun j => hc.choose.1 (τ j) := funext fun j => congrArg Prod.fst (hτ j)
    have hy : y = fun j => hc.choose.2 (τ j) := funext fun j => congrArg Prod.snd (hτ j)
    rw [Submodule.coe_zero, Matrix.zero_apply]
    calc (T : Matrix _ _ ℂ) x y =
          (T : Matrix _ _ ℂ) (fun j => hc.choose.1 (τ j)) (fun j => hc.choose.2 (τ j)) :=
          congrArg₂ _ hx hy
      _ = (T : Matrix _ _ ℂ) hc.choose.1 hc.choose.2 := commutant_apply_perm ι k T.2 τ _ _
      _ = 0 := h0
  calc Module.finrank ℂ (commutant ι k) ≤ Module.finrank ℂ (Z → ℂ) :=
        LinearMap.finrank_le_finrank_of_injective hΛ
    _ = (k + 1) ^ (Fintype.card Y ^ 2) := by
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_prod, sq]

/-- The images `e^λ_{ij}` of the matrix units of `ℂ[S_k]` on `𝒱^{⊗k}`. -/
noncomputable def eU (l : IrrepLabel (Equiv.Perm (Fin k))) (i j : Fin l.dim) :
    Matrix (Config ι k) (Config ι k) ℂ :=
  groupAlgebraRep (copyPerm ι k Finset.univ) (IrrepLabel.matrixUnit l i j)

theorem eU_mul_eU (l : IrrepLabel (Equiv.Perm (Fin k))) (i j j' m : Fin l.dim) :
    eU ι k l i j * eU ι k l j' m = if j = j' then eU ι k l i m else 0 := by
  simp only [eU, ← map_mul, IrrepLabel.matrixUnit_mul_matrixUnit]
  split_ifs <;> simp

theorem eU_mul_eU_of_ne {l l' : IrrepLabel (Equiv.Perm (Fin k))} (h : l ≠ l') (i j : Fin l.dim)
    (i' j' : Fin l'.dim) : eU ι k l i j * eU ι k l' i' j' = 0 := by
  rw [eU, eU, ← map_mul, IrrepLabel.matrixUnit_mul_matrixUnit_of_ne h, map_zero]

/-- `Tr π^λ = d_λ Tr e^λ_{i₀i₀}`. -/
theorem trace_π_eq (l : IrrepLabel (Equiv.Perm (Fin k))) (i₀ : Fin l.dim) :
    trace (π ι k Finset.univ l) = l.dim * trace (eU ι k l i₀ i₀) := by
  have hsum : π ι k Finset.univ l = ∑ i, eU ι k l i i := by
    simp only [eU, ← map_sum, IrrepLabel.sum_matrixUnit_diag]; rfl
  have htr : ∀ i, trace (eU ι k l i i) = trace (eU ι k l i₀ i₀) := fun i => by
    have h1 : eU ι k l i i₀ * eU ι k l i₀ i = eU ι k l i i := by rw [eU_mul_eU, if_pos rfl]
    have h2 : eU ι k l i₀ i * eU ι k l i i₀ = eU ι k l i₀ i₀ := by rw [eU_mul_eU, if_pos rfl]
    rw [← h1, trace_mul_comm, h2]
  rw [hsum, trace_sum, Finset.sum_congr rfl fun i _ => htr i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-- `∑_j e^λ_{j i₀} N e^λ_{i₀ j}` commutes with the `S_k` action, for every `N`. -/
theorem commute_sum_eU (l : IrrepLabel (Equiv.Perm (Fin k))) (i₀ : Fin l.dim)
    (N : Matrix (Config ι k) (Config ι k) ℂ) (σ : Equiv.Perm (Fin k)) :
    Commute (U ι k Finset.univ σ) (∑ j, eU ι k l j i₀ * N * eU ι k l i₀ j) := by
  suffices h : ∀ a, Commute (groupAlgebraRep (copyPerm ι k Finset.univ) a)
      (∑ j, eU ι k l j i₀ * N * eU ι k l i₀ j) by
    simpa [U] using h (single σ 1)
  intro a
  rw [IrrepLabel.eq_sum_matrixUnit a]
  simp only [map_sum, map_smul]
  refine Commute.sum_left _ _ _ fun μ _ => Commute.sum_left _ _ _ fun i _ =>
    Commute.sum_left _ _ _ fun m _ => Commute.smul_left ?_ _
  change Commute (eU ι k μ i m) _
  rw [Commute, SemiconjBy, Finset.mul_sum, Finset.sum_mul]
  by_cases h : μ = l
  · subst h
    have hL : ∀ j, eU ι k μ i m * (eU ι k μ j i₀ * N * eU ι k μ i₀ j) =
        if m = j then eU ι k μ i i₀ * N * eU ι k μ i₀ m else 0 := by
      intro j
      rw [← mul_assoc, ← mul_assoc, eU_mul_eU]
      split_ifs with hj
      · subst hj; rfl
      · simp
    have hR : ∀ j, eU ι k μ j i₀ * N * eU ι k μ i₀ j * eU ι k μ i m =
        if j = i then eU ι k μ i i₀ * N * eU ι k μ i₀ m else 0 := by
      intro j
      rw [mul_assoc, eU_mul_eU]
      split_ifs with hj
      · subst hj; rfl
      · simp
    rw [Finset.sum_congr rfl fun j _ => hL j, Finset.sum_congr rfl fun j _ => hR j,
      Finset.sum_ite_eq, Finset.sum_ite_eq']
    simp
  · refine (Finset.sum_eq_zero fun j _ => ?_).trans (Finset.sum_eq_zero fun j _ => ?_).symm
    · rw [← mul_assoc, ← mul_assoc, eU_mul_eU_of_ne ι k h, zero_mul, zero_mul]
    · rw [mul_assoc, eU_mul_eU_of_ne ι k (Ne.symm h), mul_zero]

/-- D6.4.16 (counting). `∑_λ dim V_λ = ∑_λ Tr π^λ / d_λ` is at most the dimension of the
commutant: `N ↦ ∑_j e^λ_{j0} N e^λ_{0j}` embeds `⨁_λ e^λ_{00}𝒱^{⊗k}` into it. -/
theorem sum_trace_π_div_le :
    ∑ l, (trace (π ι k Finset.univ l)).re / l.dim ≤ Module.finrank ℂ (commutant ι k) := by
  classical
  let i0 : ∀ l : IrrepLabel (Equiv.Perm (Fin k)), Fin l.dim := fun l => ⟨0, l.dim_pos⟩
  have hE : ∀ l, eU ι k l (i0 l) (i0 l) * eU ι k l (i0 l) (i0 l) = eU ι k l (i0 l) (i0 l) :=
    fun l => by rw [eU_mul_eU, if_pos rfl]
  let R : ∀ l : IrrepLabel (Equiv.Perm (Fin k)), Submodule ℂ (Config ι k → ℂ) :=
    fun l => LinearMap.range (Matrix.toLin' (eU ι k l (i0 l) (i0 l)))
  have hR : ∀ l, ∀ r ∈ R l, eU ι k l (i0 l) (i0 l) *ᵥ r = r := by
    rintro l _ ⟨x, rfl⟩
    rw [Matrix.toLin'_apply, mulVec_mulVec, hE]
  have hterm : ∀ l, (trace (π ι k Finset.univ l)).re / l.dim =
      Module.finrank ℂ (R l) := by
    intro l
    have hid : IsIdempotentElem (Matrix.toLin' (eU ι k l (i0 l) (i0 l))) := by
      rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hE]
    have hd : (l.dim : ℝ) ≠ 0 := mod_cast l.dim_pos.ne'
    rw [trace_π_eq ι k l (i0 l), ← Matrix.trace_toLin'_eq,
      (LinearMap.IsIdempotentElem.isProj_range _ hid).trace]
    simp only [Complex.natCast_re, Complex.mul_re, Complex.natCast_im, zero_mul, sub_zero]
    field_simp
    rfl
  have hy : ∀ l, ∃ y : Config ι k → ℂ, y ᵥ* eU ι k l (i0 l) (i0 l) = y ∧
      (eU ι k l (i0 l) (i0 l) ≠ 0 → y ≠ 0) := by
    intro l
    by_cases h : eU ι k l (i0 l) (i0 l) = 0
    · exact ⟨0, by simp, fun h' => absurd h h'⟩
    obtain ⟨a, b, hab⟩ : ∃ a b, eU ι k l (i0 l) (i0 l) a b ≠ 0 := by
      contrapose! h; exact Matrix.ext h
    refine ⟨Pi.single a 1 ᵥ* eU ι k l (i0 l) (i0 l), by rw [vecMul_vecMul, hE],
      fun _ hy0 => hab ?_⟩
    simpa [vecMul, dotProduct, Pi.single_apply] using congrFun hy0 b
  choose y hy1 hy2 using hy
  let T : ∀ l : IrrepLabel (Equiv.Perm (Fin k)), (Config ι k → ℂ) →
      Matrix (Config ι k) (Config ι k) ℂ := fun l r =>
    ∑ j, eU ι k l j (i0 l) * vecMulVec r (y l) * eU ι k l (i0 l) j
  let Φ : (Π l, R l) →ₗ[ℂ] commutant ι k :=
    { toFun := fun r => ⟨∑ l, T l (r l), fun σ =>
        Commute.sum_right _ _ _ fun l _ => commute_sum_eU ι k l (i0 l) _ σ⟩
      map_add' := fun r r' => by
        apply Subtype.ext
        simp only [T, Pi.add_apply, Submodule.coe_add, add_vecMulVec, mul_add, add_mul,
          Finset.sum_add_distrib]
      map_smul' := fun c r => by
        apply Subtype.ext
        simp only [T, Pi.smul_apply, Submodule.coe_smul, smul_vecMulVec, mul_smul_comm,
          smul_mul_assoc, Finset.smul_sum, RingHom.id_apply] }
  have hext : ∀ (r : Π l, R l) μ, eU ι k μ (i0 μ) (i0 μ) * (Φ r : Matrix _ _ ℂ) *
      eU ι k μ (i0 μ) (i0 μ) = vecMulVec (r μ) (y μ) := by
    intro r μ
    change eU ι k μ (i0 μ) (i0 μ) * (∑ l, T l (r l)) * eU ι k μ (i0 μ) (i0 μ) = _
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_eq_single μ]
    · simp only [T]
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_eq_single (i0 μ)]
      · rw [← mul_assoc, ← mul_assoc, hE, mul_assoc, hE, mul_vecMulVec, vecMulVec_mul,
          hR μ _ (r μ).2, hy1]
      · intro j _ hj
        rw [← mul_assoc, ← mul_assoc, eU_mul_eU, if_neg (Ne.symm hj), zero_mul, zero_mul,
          zero_mul]
      · simp
    · intro l _ hl
      simp only [T]
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [← mul_assoc, ← mul_assoc, eU_mul_eU_of_ne ι k (Ne.symm hl), zero_mul, zero_mul,
        zero_mul]
    · simp
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro r hr
    funext μ
    apply Subtype.ext
    have h := hext r μ
    rw [hr, Submodule.coe_zero, mul_zero, zero_mul, eq_comm, vecMulVec_eq_zero] at h
    rcases h with h | h
    · exact h
    · by_cases hE0 : eU ι k μ (i0 μ) (i0 μ) = 0
      · rw [← hR μ _ (r μ).2, hE0, zero_mulVec]; rfl
      · exact absurd h (hy2 μ hE0)
  rw [Finset.sum_congr rfl fun l _ => hterm l]
  exact_mod_cast Module.finrank_pi_fintype (R := ℂ) (ι := IrrepLabel (Equiv.Perm (Fin k)))
    (M := fun l => R l) ▸ LinearMap.finrank_le_finrank_of_injective hΦ

/-- D6.4.16. Block `λ`, eigenvalue `u` contributes `d_λ·u·(u d_λ)^{-b} = (u d_λ)^{1-b} ≤ 1`
(`1 - b ≥ 0`). So `Tr ρ e^{b(L_ρ - F_Q)} = ∑_λ ∑_{u>0} (u d_λ)^{1-b} ≤ ∑_λ dim V_λ ≤ poly(k)`;
here `poly(k) = (k+1)^{q²}`, `q = dim 𝒱`. -/
theorem step_6_4_16 {ρ : Matrix (Config ι k) (Config ι k) ℂ} (hρ : ρ.PosSemidef)
    (htr : (trace ρ).re ≤ 1) (hinv : ∀ σ, Commute (U ι k Finset.univ σ) ρ) {b : ℝ}
    (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    (trace (ρ * cfc Real.exp (b • (L ρ - F ι k Finset.univ)))).re ≤
      ((k : ℝ) + 1) ^ (Fintype.card ((f : I) → ι f) ^ 2) :=
  calc _ ≤ ∑ l, (trace (π ι k Finset.univ l)).re / l.dim :=
        trace_mul_exp_le_sum_dim ι k hρ htr hinv hb
    _ ≤ Module.finrank ℂ (commutant ι k) := sum_trace_π_div_le ι k
    _ ≤ ((k + 1) ^ (Fintype.card ((f : I) → ι f) ^ 2) : ℕ) := by
      exact_mod_cast finrank_commutant_le ι k
    _ = _ := by push_cast; ring

/-- D6.4 (5). Let `ρ` be a permutation-invariant density on `𝒱^{⊗k}` and `L_ρ = -log ρ` on
`supp ρ`. Then `[F, ρ] = 0`, `0 ≤ F ≤ L_ρ` on the support, and for `0 ≤ b ≤ 1`
`Tr ρ e^{b(L_ρ - F)} ≤ poly(k)`, the polynomial depending only on `dim 𝒱`. -/
theorem lemma_6_1_5 : ∃ C N : ℕ, ∀ (k : ℕ) (ρ : Matrix (Config ι k) (Config ι k) ℂ),
    ρ.PosSemidef → (trace ρ).re ≤ 1 → (∀ σ, Commute (U ι k Finset.univ σ) ρ) →
      Commute (F ι k Finset.univ) ρ ∧ (F ι k Finset.univ).PosSemidef ∧
      suppProj ρ * F ι k Finset.univ * suppProj ρ ≤ L ρ ∧
      ∀ b ∈ Set.Icc (0 : ℝ) 1, (trace (ρ * cfc Real.exp (b • (L ρ - F ι k Finset.univ)))).re ≤
        C * ((k : ℝ) + 1) ^ N := by
  refine ⟨1, Fintype.card ((f : I) → ι f) ^ 2, fun k ρ hρ htr hinv =>
    ⟨(step_6_4_15 ι k hρ htr hinv).1, (step_6_4_15 ι k hρ htr hinv).2.1,
      (step_6_4_15 ι k hρ htr hinv).2.2, fun b hb => ?_⟩⟩
  -- D6.4.16
  simpa using step_6_4_16 ι k hρ htr hinv hb

end Surprisal

end AreaLaw.Replicas
