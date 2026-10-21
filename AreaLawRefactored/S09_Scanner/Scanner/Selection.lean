import AreaLawRefactored.S09_Scanner.Scanner.Entropy
import AreaLawForMathlib.Analysis.Matrix.FilteredNormFloor

/-!
# §9.2 Integration over the rounds and selection of `(round, p_k)` (D9.12)

Digest `digest/09-scanner.md` D9.12, paper `paper/sections/08-scanner.tex` 457–490. Graph-level
(Map.md, Dimension: `any d`).

Proposition 7.4 (b) is pointwise in `p`, and only the exact derivative is known to be
integrable; the selection is therefore argued by contradiction (D9.12.4–D9.12.6 with the plain
averaging replaced by its contrapositive): if every charge round and every `p ∈ [ε/2, ε]` had a
large `𝒬(p)`, the pointwise bound integrated over `[ε/2, ε]` and telescoped over all rounds
would exceed the initial and final norms.
-/

open scoped Matrix ComplexOrder MatrixOrder
open Finset MeasureTheory Arealaw Entropy Set

namespace AreaLaw.Scanner

open Transport (Round EnergyTerms PYF MeanTree)
open Comparators (physReg dims)

universe u

/-! ## D9.12.2 The floor of the metric -/

section Floor

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ} [∀ v, NeZero (n v)]

omit [∀ v, NeZero (n v)] in
/-- A floor `b Π_k ≤ A_k(P, Y, F)` on `𝒮_k`, `b ≤ 1`, is a floor `b ≤ Π_k A + (1 - Π_k)` of the
band metric on the whole space. -/
theorem smul_one_le_bandMetric {π : PYF V} {t b : ℝ} (hb1 : b ≤ 1) (k : ℕ)
    (hA : b • Replicas.projS (fun v => Fin (n v)) k ≤
      Replicas.A (fun v => Fin (n v)) t k π.P π.Y π.F) :
    b • (1 : Matrix (Transport.Config n k) (Transport.Config n k) ℂ) ≤
      Transport.bandMetric n t k π := by
  set P := Transport.Pi n k
  set A := Replicas.A (fun v => Fin (n v)) t k π.P π.Y π.F
  have hPS : Replicas.projS (fun v => Fin (n v)) k = P := (Transport.Pi_eq_projS n k).symm
  rw [hPS] at hA
  have hPP : P * P = P := Transport.Pi_mul_Pi k
  have hPh : Pᴴ = P := (Transport.isHermitian_Pi k).eq
  have hAP : A * P = P * A := (Transport.commute_Pi_A t k π.P π.Y π.F).eq.symm
  have hP1 : (1 - P).PosSemidef := Matrix.nonneg_iff_posSemidef.1
    (PermutationRepresentation.isStarProjection_symProj _).one_sub.nonneg
  have key : Transport.bandMetric n t k π - b • 1 =
      Pᴴ * (A - b • P) * P + (1 - b) • (1 - P) := by
    rw [hPh, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hPP, hPP,
      Matrix.mul_assoc, hAP, ← Matrix.mul_assoc, hPP]
    simp only [Transport.bandMetric]
    module
  rw [Matrix.le_iff, key]
  exact ((Matrix.le_iff.1 hA).conjTranspose_mul_mul_same P).add
    (hP1.smul (by linarith))

variable {K : ℕ} {H : Type*} [Fintype H] [DecidableEq H] {C : H → Type*} [∀ h, Fintype (C h)]
  [∀ h, DecidableEq (C h)] (R : Round V K H C)

set_option linter.unusedFintypeInType false in
/-- D9.12.2. A floor `b Π_k ≤ A_k` of every band metric of a partition gives the floor
`b^K ≤ 𝓜(p)` of the root (Lemma 7.1 (5): mean trees preserve the floor). -/
theorem smul_one_le_root (hR : R.IsAdmissible) {t b : ℝ} (ht : 0 ≤ t) (hb0 : 0 < b)
    (hb1 : b ≤ 1) {k : ℕ} (hcomm : R.CrossBandCommute n t k)
    (hfloor : ∀ π : PYF V, π.IsPartition → b • Replicas.projS (fun v => Fin (n v)) k ≤
      Replicas.A (fun v => Fin (n v)) t k π.P π.Y π.F) (p : ℝ) :
    b ^ K • (1 : Matrix (Transport.Config n k) (Transport.Config n k) ℂ) ≤ R.root n t k p := by
  have hleaf : ∀ j, b ^ K • (1 : Matrix (Transport.Config n k) (Transport.Config n k) ℂ) ≤
      R.input n t k j := fun j => by
    rw [Round.input_eq_prod]
    have h := Matrix.pow_smul_one_le_list_prod hb0.le (l := List.ofFn fun g =>
      Transport.bandMetric n t k (R.leafPart j g)) (fun A hA => by
        obtain ⟨g, rfl⟩ := List.mem_ofFn.1 hA
        exact smul_one_le_bandMetric hb1 k (hfloor _ (R.isPartition_leafPart hR j g)))
      (List.pairwise_ofFn.2 fun g g' hgg' => hcomm j j g g' (ne_of_lt hgg'))
    rwa [List.length_ofFn] at h
  have h := Transport.lemma_7_1_5 (R.posDef_input hR ht hcomm)
    (P := (1 : Matrix (Transport.Config n k) (Transport.Config n k) ℂ)) (IsStarProjection.one _)
    (c := fun _ => b ^ K) (fun _ => pow_pos hb0 K) hleaf
    (R.tree (projIcc (0 : ℝ) 1 zero_le_one p))
  rwa [← Real.rpow_sum_of_pos (pow_pos hb0 K), MeanTree.sum_weight, Real.rpow_one] at h

set_option linter.unusedFintypeInType false in
/-- D9.12.2. With the leaf floor `(k + 2)^{-C₀} Π_k ≤ A_k` (D6.9) and `‖pre‖ ≤ 1`:
`log N(p)² ≤ (K/2) C₀ log(k + 2)`. -/
theorem log_normSq_le_of_floor (hR : R.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    (hcomm : R.CrossBandCommute n t k) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hfloor : ∀ π : PYF V, π.IsPartition → (((k : ℝ) + 2) ^ (-C₀)) •
      Replicas.projS (fun v => Fin (n v)) k ≤ Replicas.A (fun v => Fin (n v)) t k π.P π.Y π.F)
    {pre : Transport.Config n k → ℂ} (hpre : pre ≠ 0) (hnorm : (star pre ⬝ᵥ pre).re ≤ 1)
    (p : ℝ) : Real.log (R.normSq n t k pre p) ≤ K / 2 * C₀ * Real.log ((k : ℝ) + 2) := by
  have hk2 : (1 : ℝ) ≤ (k : ℝ) + 2 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  set b := ((k : ℝ) + 2) ^ (-C₀)
  have hb0 : 0 < b := Real.rpow_pos_of_pos (by linarith) _
  have hb1 : b ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hk2 (by linarith)
  have hM := R.posDef_root hR ht hcomm p
  have hfl := smul_one_le_root R hR ht hb0 hb1 hcomm hfloor p
  have hN := Matrix.Transport.filteredNormSq_pos hM hpre
  have hle := Matrix.Transport.filteredNormSq_le_of_smul_one_le hM (pow_pos hb0 K) hfl pre
  have hc : 0 < (b ^ K) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (pow_pos hb0 K) _
  have h1 : R.normSq n t k pre p ≤ ((b ^ K) ^ (1 / 2 : ℝ))⁻¹ := by
    refine hle.trans ?_
    calc ((b ^ K) ^ (1 / 2 : ℝ))⁻¹ * (star pre ⬝ᵥ pre).re ≤ ((b ^ K) ^ (1 / 2 : ℝ))⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hnorm (inv_nonneg.2 hc.le)
      _ = _ := mul_one _
  have h2 : Real.log (((b ^ K) ^ (1 / 2 : ℝ))⁻¹) = K / 2 * C₀ * Real.log ((k : ℝ) + 2) := by
    rw [Real.log_inv, Real.log_rpow (pow_pos hb0 K), Real.log_pow,
      Real.log_rpow (by linarith)]
    ring
  rw [← h2]
  exact Real.log_le_log hN h1

end Floor

/-! ## D9.12.1 Telescoping -/

/-- D9.12.1, D9.12.4. Telescoping the endpoint identities of `N` rounds chained at their
endpoints: if each exact derivative is `≥ -e_t` on `(0, 1)` and, on the rounds of `P`, `≥ G - e_t`
on `(ε/2, ε)`, then `log N₀(0)² - log N_{last}(1)² ≥ #P (ε/2) G - ∑_t e_t`. -/
theorem telescope_rounds {N : ℕ} (hN : 0 < N) {f ED : ℕ → ℝ → ℝ} {e : ℕ → ℝ} {P : ℕ → Prop}
    [DecidablePred P] {ε G : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hchain : ∀ t, t + 1 < N → f t 1 = f (t + 1) 0)
    (hid : ∀ t < N, ∀ p₀ p₁ : ℝ, 0 ≤ p₀ → p₀ ≤ p₁ → p₁ ≤ 1 →
      IntervalIntegrable (ED t) volume p₀ p₁ ∧
        Real.log (f t p₀) - Real.log (f t p₁) = ∫ p in p₀..p₁, ED t p)
    (hlow : ∀ t < N, ∀ p ∈ Ioo (0 : ℝ) 1, -e t ≤ ED t p)
    (hgain : ∀ t < N, P t → ∀ p ∈ Ioo (ε / 2) ε, G - e t ≤ ED t p) :
    ∑ t ∈ range N, ((if P t then ε / 2 * G else 0) - e t) ≤
      Real.log (f 0 0) - Real.log (f (N - 1) 1) := by
  -- one round: split `[0, 1]` at `ε/2` and `ε`
  have hround : ∀ t < N, (if P t then ε / 2 * G else 0) - e t ≤
      Real.log (f t 0) - Real.log (f t 1) := by
    intro t ht
    have hc : ∀ (p₀ p₁ c : ℝ), 0 ≤ p₀ → p₀ ≤ p₁ → p₁ ≤ 1 → (∀ p ∈ Ioo p₀ p₁, c ≤ ED t p) →
        c * (p₁ - p₀) ≤ Real.log (f t p₀) - Real.log (f t p₁) := by
      intro p₀ p₁ c h0 h01 h1 hcp
      rw [(hid t ht p₀ p₁ h0 h01 h1).2]
      have := intervalIntegral.integral_mono_on_of_le_Ioo h01 intervalIntegrable_const
        (hid t ht p₀ p₁ h0 h01 h1).1 hcp
      rwa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] at this
    have hlo : ∀ p₀ p₁ : ℝ, 0 ≤ p₀ → p₀ ≤ p₁ → p₁ ≤ 1 →
        -e t * (p₁ - p₀) ≤ Real.log (f t p₀) - Real.log (f t p₁) := fun p₀ p₁ h0 h01 h1 =>
      hc p₀ p₁ _ h0 h01 h1 fun p hp => hlow t ht p ⟨h0.trans_lt hp.1, hp.2.trans_le h1⟩
    have h1 := hlo 0 (ε / 2) le_rfl (by linarith) (by linarith)
    have h3 := hlo ε 1 hε0.le hε1 le_rfl
    split_ifs with hP
    · have h2 := hc (ε / 2) ε (G - e t) (by linarith) (by linarith) hε1 (hgain t ht hP)
      nlinarith
    · have h2 := hlo (ε / 2) ε (by linarith) (by linarith) hε1
      nlinarith
  -- the chain `f_t(1) = f_{t+1}(0)`
  have htel : ∀ M, 0 < M → M ≤ N → ∑ t ∈ range M, (Real.log (f t 0) - Real.log (f t 1)) =
      Real.log (f 0 0) - Real.log (f (M - 1) 1) := by
    intro M hM hMN
    induction M with
    | zero => omega
    | succ M ih =>
      rcases Nat.eq_zero_or_pos M with rfl | hM'
      · simp
      · rw [sum_range_succ, ih hM' (by omega), hchain (M - 1) (by omega),
          Nat.sub_add_cancel hM', Nat.add_sub_cancel]
        ring
  rw [← htel N hN le_rfl]
  exact sum_le_sum fun t ht => hround t (mem_range.1 ht)

theorem sum_range_odd (M : ℕ) (x : ℝ) :
    ∑ t ∈ range (2 * M), (if t % 2 = 1 then x else 0) = M * x := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih]
    have h1 : (2 * M) % 2 = 0 := by omega
    have h2 : (2 * M + 1) % 2 = 1 := by omega
    rw [if_neg (by omega), if_pos h2]
    push_cast
    ring

/-! ## The rounds and the global statuses -/

section Bridge

variable {σ : Type u} [DecidableEq σ] (S : Scan σ)

variable {nq : S.Λ → ℕ} {d : ℕ}

theorem leafA_mk (τ : ℝ) (k : ℕ) (t : Fin S.T)
    (j : Round.Leaf (S.Hist t) (fun _ => S.Ch t)) :
    S.Γ.leafA nq d τ k ⟨t, j⟩ = (S.round t).input (dims nq d) τ k j := by
  rw [Round.input_eq_prod]
  simp only [Comparators.Statuses.leafA, Comparators.Statuses.bandA, S.round_leafPart]

/-- D9.7. The root of the terminal tree of round `t` at `p`, relabelled into the global status
type, is the interpolated root `𝓜(p)` of the round. -/
theorem root_map (τ : ℝ) (k : ℕ) (t : Fin S.T) (p : unitInterval) :
    S.Γ.root nq d (((S.round t).tree p).map (Sigma.mk t)) τ k =
      (S.round t).root (dims nq d) τ k p := by
  simp only [Comparators.Statuses.root, Round.root, Set.projIcc_val, MeanTree.eval_map]
  congr 1
  funext j
  exact leafA_mk S τ k t j

variable (Dt : Comparators.PhysData nq) (E : Comparators.TypicalSet Dt S.X)

theorem N2_map (a : ℝ) (k : ℕ) (l : IrrepLabel (Equiv.Perm (Fin k))) (t : Fin S.T)
    (p : unitInterval) :
    Comparators.N2 Dt S.Γ E (((S.round t).tree p).map (Sigma.mk t)) a k l =
      (S.round t).normSq (dims nq E.d) (a / 2) k (Comparators.pre Dt E.d k l) p := by
  simp only [Comparators.N2, Round.normSq, root_map]

theorem Edef_map (a : ℝ) (k : ℕ) (l : IrrepLabel (Equiv.Perm (Fin k))) (t : Fin S.T)
    (p : unitInterval) :
    Comparators.Edef Dt S.Γ E (((S.round t).tree p).map (Sigma.mk t)) a k l =
      ((star ((S.round t).v (dims nq E.d) (a / 2) k (Comparators.pre Dt E.d k l) p) ⬝ᵥ
        (Comparators.Hbar Dt E.d k *ᵥ
          (S.round t).v (dims nq E.d) (a / 2) k (Comparators.pre Dt E.d k l) p)).re - Dt.E₀) /
        Dt.g := by
  simp only [Comparators.Edef, Comparators.vec, Round.v, root_map]

end Bridge

/-! ## D9.12.1 The rounds are chained -/

section Chain

variable {σ : Type u} [DecidableEq σ] (S : Scan σ) {n : Comparators.Site S.Λ → ℕ}
  [∀ v, NeZero (n v)]

/-- D9.12.1. Adjacent endpoint metrics agree: `𝓜_t(1) = 𝓜_{t+1}(0)`. -/
theorem root_one_eq_root_zero (t : Fin S.T) (ht : t.1 + 1 < S.T) {τ : ℝ} (hτ : 0 ≤ τ) {k : ℕ}
    (hc : (S.round t).CrossBandCommute n τ k)
    (hc' : (S.round ⟨t + 1, ht⟩).CrossBandCommute n τ k) :
    (S.round t).root n τ k 1 = (S.round ⟨t + 1, ht⟩).root n τ k 0 := by
  have hR := S.round_isAdmissible t
  have hR' := S.round_isAdmissible ⟨t + 1, ht⟩
  rw [show (1 : ℝ) = ((1 : unitInterval) : ℝ) from rfl,
    show (0 : ℝ) = ((0 : unitInterval) : ℝ) from rfl, Round.root_eq, Round.root_eq]
  have e1 : ∀ h, Matrix.geomMean ((1 : unitInterval) : ℝ) ((S.round t).oldMetric n τ k h)
      ((S.round t).choiceRoot n τ k h) = (S.round t).choiceRoot n τ k h := fun h =>
    Matrix.geomMean_one ((S.round t).posDef_input hR hτ hc ⟨h, none⟩)
      ((S.round t).posDef_choiceRoot hR hτ hc h)
  have e0 : ∀ h, Matrix.geomMean ((0 : unitInterval) : ℝ)
      ((S.round ⟨t + 1, ht⟩).oldMetric n τ k h) ((S.round ⟨t + 1, ht⟩).choiceRoot n τ k h) =
      (S.round ⟨t + 1, ht⟩).oldMetric n τ k h := fun h =>
    Matrix.geomMean_zero ((S.round ⟨t + 1, ht⟩).posDef_input hR' hτ hc' ⟨h, none⟩)
      ((S.round ⟨t + 1, ht⟩).posDef_choiceRoot hR' hτ hc' h)
  simp only [e1, e0]
  rw [S.round_histTree_succ t ht, MeanTree.eval_bind]
  refine congrArg (fun f => MeanTree.eval f (S.round t).histTree) (funext fun h => ?_)
  rw [MeanTree.eval_map, Round.choiceRoot]
  refine congrArg (fun f => MeanTree.eval f ((S.round t).choiceTree h)) (funext fun c => ?_)
  simp only [Function.comp_apply, Round.oldMetric, Round.newMetric, S.round_old_succ t ht h c]

end Chain

/-! ## D9.12 Selection of `(round, p_k)` -/

section Selection

variable {σ : Type u} [DecidableEq σ] (S : Scan σ) {nl : Comparators.Site S.Λ → ℕ}
  [∀ v, NeZero (nl v)] (E : EnergyTerms (Comparators.Site S.Λ) nl S.Term)

/-- D9.12 (`scanner:selected-density`). There are a charge round and `p_k ∈ [ε/2, ε]` with
`𝒬(p_k)/(KnD) ≤ δ'`, where `δ'` is the total entropy budget of the scan divided by the
production rate: the initial norm `log N²_init ≤ B_init` (D9.12.2), the final norm
`-log N²_end ≤ B_fin` (D9.12.3, `comparator:rough-upper`) and the errors `Err_t` of Proposition
7.4 (b) on the `2nm` rounds (D9.12.4), against the gain `(c k a/(nD)) 𝒬` of D9.11 on the `nm`
charge rounds over `[ε/2, ε]` (D9.12.5), plus `1/k`. -/
theorem step_9_12 (hE : S.HasSupports E) {c₁ : ℝ} (hc₁ : 0 < c₁) (h4 : S.Item4 c₁)
    (hn : 1 ≤ S.n) (hm : 1 ≤ S.m) (hK : 1 ≤ S.K) (hD : 1 ≤ S.D) {a ε : ℝ} (ha : 0 < a)
    (hε0 : 0 < ε) (hε1 : ε < 1) {k : ℕ} (hk : 0 < k) {pre : Transport.Config nl k → ℂ}
    (hpreS : pre ∈ Replicas.S (fun v => Fin (nl v)) k) (hpre : pre ≠ 0)
    (hcomm : ∀ t, (S.round t).CrossBandCommute nl (a / 2) k) (Err : Fin S.T → ℝ)
    (hb : ∀ (t : Fin S.T) (p : unitInterval), 0 < (p : ℝ) → (p : ℝ) < 1 →
      (k : ℝ) * a * (S.round t).entropyGain nl (a / 2) k pre p - Err t ≤
        (S.round t).exactDerivative nl (a / 2) k pre p)
    (hid : ∀ (t : Fin S.T) (p₀ p₁ : ℝ), 0 ≤ p₀ → p₀ ≤ p₁ → p₁ ≤ 1 →
      IntervalIntegrable (fun p => (S.round t).exactDerivative nl (a / 2) k pre
          (projIcc 0 1 zero_le_one p)) volume p₀ p₁ ∧
        Real.log ((S.round t).normSq nl (a / 2) k pre p₀) -
            Real.log ((S.round t).normSq nl (a / 2) k pre p₁) =
          ∫ p in p₀..p₁, (S.round t).exactDerivative nl (a / 2) k pre (projIcc 0 1 zero_le_one p))
    {Binit Bfin : ℝ} (hT : 0 < S.T)
    (hinit : Real.log ((S.round ⟨0, hT⟩).normSq nl (a / 2) k pre 0) ≤ Binit)
    (hfin : -Real.log ((S.round ⟨S.T - 1, by omega⟩).normSq nl (a / 2) k pre 1) ≤ Bfin) :
    ∃ t : Fin S.T, t.1 % 2 = 1 ∧ ∃ p : unitInterval, ε / 2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ ε ∧
      step_9_10 (S.round t) E (S.Good t) (a / 2) k pre p ≤
        S.K * S.n * S.D * ((Binit + Bfin + ∑ t, Err t) /
          (S.n * S.m * (ε / 2) * k * a * c₁ * S.K) + 1 / k) := by
  set δ := (Binit + Bfin + ∑ t, Err t) / (S.n * S.m * (ε / 2) * k * a * c₁ * S.K) + 1 / k
  by_contra hcon
  push Not at hcon
  have hn' : (1 : ℝ) ≤ S.n := by exact_mod_cast hn
  have hm' : (1 : ℝ) ≤ S.m := by exact_mod_cast hm
  have hK' : (1 : ℝ) ≤ S.K := by exact_mod_cast hK
  have hD' : (1 : ℝ) ≤ S.D := by exact_mod_cast hD
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  -- the rounds indexed by `ℕ`
  set F : ℕ → ℝ → ℝ := fun t p =>
    if h : t < S.T then (S.round ⟨t, h⟩).normSq nl (a / 2) k pre p else 1
  set ED : ℕ → ℝ → ℝ := fun t p => if h : t < S.T then
    (S.round ⟨t, h⟩).exactDerivative nl (a / 2) k pre (projIcc 0 1 zero_le_one p) else 0
  set e : ℕ → ℝ := fun t => if h : t < S.T then Err ⟨t, h⟩ else 0
  set G := (k : ℝ) * a * c₁ * S.K * δ
  have hpt : ∀ p ∈ Ioo (0 : ℝ) 1, (projIcc (0 : ℝ) 1 zero_le_one p : ℝ) = p := fun p hp => by
    rw [projIcc_of_mem _ ⟨hp.1.le, hp.2.le⟩]
  have hT1 : S.T - 1 < S.T := by omega
  have key := telescope_rounds (N := S.T) (f := F) (ED := ED) (e := e)
    (P := fun t => t % 2 = 1) (G := G) hT hε0 hε1.le
    (fun t ht => by
      -- D9.12.1: adjacent endpoint metrics agree
      simp only [F, dif_pos ht, dif_pos (by omega : t < S.T), Round.normSq]
      rw [root_one_eq_root_zero S ⟨t, by omega⟩ ht (by positivity) (hcomm _) (hcomm _)])
    (fun t ht p₀ p₁ h0 h01 h1 => by
      simp only [F, ED, dif_pos ht]
      exact hid ⟨t, ht⟩ p₀ p₁ h0 h01 h1)
    (fun t ht p hp => by
      simp only [ED, e, dif_pos ht]
      have hp' := hpt p hp
      refine (step_9_11 S E hE hc₁.le h4 ⟨t, ht⟩ ha.le (hcomm _) hpreS hpre
        (p := projIcc 0 1 zero_le_one p) (by rw [hp']; exact hp.1) (by rw [hp']; exact hp.2)
        (hb _ _ (by rw [hp']; exact hp.1) (by rw [hp']; exact hp.2))).2)
    (fun t ht hP p hp => by
      simp only [ED, e, dif_pos ht]
      have hp0 : p ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp.1], by linarith [hp.2]⟩
      have hp' := hpt p hp0
      have h := (step_9_11 S E hE hc₁.le h4 ⟨t, ht⟩ ha.le (hcomm _) hpreS hpre
        (p := projIcc 0 1 zero_le_one p) (by rw [hp']; exact hp0.1) (by rw [hp']; exact hp0.2)
        (hb _ _ (by rw [hp']; exact hp0.1) (by rw [hp']; exact hp0.2))).1 hP
      -- D9.12.5: `𝒬(p)/(KnD) > δ` on the charge rounds
      have hQ := hcon ⟨t, ht⟩ hP (projIcc 0 1 zero_le_one p) (by rw [hp']; exact hp.1.le)
        (by rw [hp']; exact hp.2.le)
      have hc : (0 : ℝ) ≤ k * a * (c₁ / (S.n * S.D)) := by positivity
      have h2 := mul_le_mul_of_nonneg_left hQ.le hc
      have e2 : (k : ℝ) * a * (c₁ / (S.n * S.D)) * (S.K * S.n * S.D * δ) = G := by
        simp only [G]; field_simp
      linarith)
  -- D9.12.4: the left side is `nm (ε/2) G - ∑_t Err_t`
  have hsum : ∑ t ∈ range S.T, ((if t % 2 = 1 then ε / 2 * G else 0) - e t) =
      S.n * S.m * (ε / 2 * G) - ∑ t, Err t := by
    have h1 : ∑ t ∈ range S.T, (if t % 2 = 1 then ε / 2 * G else 0) =
        S.n * S.m * (ε / 2 * G) := by
      rw [Scan.T_eq, sum_range_odd]; push_cast; ring
    have h2 : ∑ t ∈ range S.T, e t = ∑ t, Err t := by
      rw [Finset.sum_range]
      exact sum_congr rfl fun t _ => dif_pos t.2
    rw [sum_sub_distrib, h1, h2]
  rw [hsum] at key
  have hF0 : F 0 0 = (S.round ⟨0, hT⟩).normSq nl (a / 2) k pre 0 := by simp only [F, dif_pos hT]
  have hF1 : F (S.T - 1) 1 = (S.round ⟨S.T - 1, hT1⟩).normSq nl (a / 2) k pre 1 := by
    simp only [F, dif_pos hT1]
  rw [hF0, hF1] at key
  -- the budget: `nm (ε/2) G = B_init + B_fin + ∑_t Err_t + nm (ε/2) k a c₁ K / k`
  have hpos : 0 < (S.n : ℝ) * S.m * (ε / 2) * k * a * c₁ * S.K := by positivity
  have hG : S.n * S.m * (ε / 2 * G) = Binit + Bfin + ∑ t, Err t +
      S.n * S.m * (ε / 2) * k * a * c₁ * S.K / k := by
    simp only [G, δ]
    field_simp
  have : 0 < (S.n : ℝ) * S.m * (ε / 2) * k * a * c₁ * S.K / k := by positivity
  linarith

end Selection

end AreaLaw.Scanner
