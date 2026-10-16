import OpenAI.Scan.SourceScan
import OpenAI.GlobalSchmidtBellRoughLower
import OpenAI.Scan.ActualTerminalPartitions
import OpenAI.Scan.ActualGlobalReplicaEnergy
import OpenAI.Scan.AugmentedRootCompression
import OpenAI.Scan.AugmentedReplicaPrevectorProperties
import OpenAI.ProjectionRangeIsometry

/-!
# The rough lower comparison along the actual charge roots

The rough lower comparison of [OAI265, Proposition 8.1, eq. (8.9)] at every actual charge root
of a collar scan, for the replica prevector of a supplied Schmidt–Bell label sequence of the
truncated ground state and total metric weight `W = 4` (per-band weight `a = 4/K`).  The defect
energy is that of the same normalized filtered vector.

`OpenAI.exists_global_schmidtBellPrevector_rough_lower` proves the comparison for any family of
nested regions and any mean tree, for the label sequence it selects; here the labels are
supplied and the regions and tree are those of the actual charge interpolation.
-/

namespace OpenAI.Scan

open Arealaw Matrix Filter TensorPower PermutationRepresentation SimpleGraph
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Topology

open CollarScan.ActualTerminals in
/-- The terminal family of a collar scan supplies disjoint near and middle regions, nesting
across bands, and the far region as the complement of their union. -/
private theorem actualTerminal_roughLower_geometry
    {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
    (S : CollarScan V I) (Horizon : ℕ) :
    let σ := CollarScan.ActualTerminals.terminalPartition S Horizon
    let Q := fun j g => receiving (σ j g) false
    let Y := fun j g => middle (σ j g)
    (∀ j g, Disjoint (Q j g) (Y j g)) ∧
      (∀ j j' g g', g < g' → Q j g ∪ Y j g ⊆ Q j' g') ∧
      (∀ j g, receiving (σ j g) true = (Q j g ∪ Y j g)ᶜ) := by
  classical
  intro σ Q Y
  have hdisj : ∀ j g, Disjoint (Q j g) (Y j g) := fun j g => by
    simp only [Q, Y, receiving, middle]
    exact Finset.disjoint_filter.mpr fun _ _ hx hy => by
      have hfalse : (some false : Option Bool) = none := hx.symm.trans hy
      cases hfalse
  have hnest : ∀ j j' g g', g < g' → Q j g ∪ Y j g ⊆ Q j' g' := fun
    | Sum.inl ⟨_, hist⟩, Sum.inl ⟨_, hist'⟩, g, g', hgg' =>
      S.state_near_middle_subset_later_near hist hist' g g' hgg'
    | Sum.inl ⟨_, hist⟩, Sum.inr ⟨_, hist'⟩, g, g', hgg' =>
      S.state_near_middle_subset_later_old_near hist hist' g g' hgg'
    | Sum.inr ⟨_, hist⟩, Sum.inl ⟨_, hist'⟩, g, g', hgg' =>
      S.old_near_middle_subset_later_state_near hist hist' g g' hgg'
    | Sum.inr ⟨_, hist⟩, Sum.inr ⟨_, hist'⟩, g, g', hgg' =>
      S.oldChargeState_near_middle_subset_later_near hist hist' g g' hgg'
  have hfar (j : terminalFamily S.K S.m S.M Horizon) (g : Fin S.K) :
      receiving (σ j g) true = (Q j g ∪ Y j g)ᶜ := by
    ext x
    cases hx : σ j g x with
    | none => simp [Q, Y, receiving, middle, hx]
    | some side => cases side <;> simp [Q, Y, receiving, middle, hx]
  exact ⟨hdisj, hnest, hfar⟩

open Classical in
/-- **The rough lower comparison at the actual charge roots** [OAI265, Proposition 8.1,
eq. (8.9), as used in eq. (9.15)].  For a unit ground vector `Ωt` of the truncated
Hamiltonian with gap `g̃ > 0`, a spectral set `E` of its target marginal and a supplied
Schmidt–Bell label sequence, there is a vanishing remainder `ρ_k` such that at all large `k`,
for every charge round `s` and parameter `p`, the defect `δ = (⟨v, \bar{H̃} v⟩ - Ẽ₀) / g̃` is
nonnegative and, for `0 < τ ≤ 1/2`,
`4 S' - 6 (τ log d + h(τ) / a) - 3 (δ / τ) max(0, 2 S') - ρ_k ≤ -k⁻¹ log N²`, where `N` is the
filtered norm, `d = |E|`, `a = 4/K` and `S'` the entropy of the selected typical vector. -/
theorem exists_actualScan_suppliedPrevector_rough_lower
    {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J : ℝ} [NeZero q] [LinearOrder (supports Λ R)]
    (S : CollarScan ↥(Λ : Set (ℤ × ℤ)) (supports Λ R)) (hm : 0 < S.m) (hM : 0 < S.M)
    (hK : 8 ≤ S.K)
    (Φ : (Y : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) Y) (Reg (Qudits q) Y) ℂ)
    (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ)) (Δ : ℝ) (L : ℕ)
    (Ωt : EuclideanSpace ℂ (Reg (Qudits q) Λ)) (e gap : ℝ) (hΩt : ‖Ωt‖ = 1)
    (hE : (∑ i, S.truncatedEnergyTerm Φ Ω J Δ L i) *ᵥ Ωt.ofLp = (e : ℂ) • Ωt.ofLp)
    (hgap : ((∑ i, S.truncatedEnergyTerm Φ Ω J Δ L i) - (e : ℂ) • 1 -
      (gap : ℂ) • (1 - vecMulVec Ωt.ofLp (star Ωt.ofLp))).PosSemidef)
    (hgap_pos : 0 < gap) (T : Finset (ℤ × ℤ))
    (E : Finset (FiniteProduct.Configuration (fun _ : ↥(Λ : Set (ℤ × ℤ)) => Fin q)
      (S.A.filter fun x => x.val ∈ T))) [NeZero E.card]
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k)))
    (hell : IsSchmidtBellLabels (∑ i, S.truncatedEnergyTerm Φ Ω J Δ L i) Ωt e
      (S.A.filter fun x => x.val ∈ T) E ell) :
    let β := fun _ : ↥(Λ : Set (ℤ × ℤ)) => Fin q
    let Xs := S.A.filter fun x => x.val ∈ T
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (FiniteProduct.splitEquiv β Xs) Ωt
    let ψ : FiniteProduct.Configuration β Xsᶜ × Fin E.card → ℂ := fun x =>
      compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
    let S' := Arealaw.vonNeumann
      (Matrix.posSemidef_vecMulVec_self_star ψ).traceLeft.isHermitian
    let d := E.card
    let a : ℝ := 4 / (S.K : ℝ)
    let nA := augmentedDimensions (V := ↥(Λ : Set (ℤ × ℤ))) q (fun _ => d)
    let pre : (k : ℕ) → Config k (fun v => Fin (nA v)) → ℂ := fun k =>
      replicaPrevector Ωt d k (ell k) ∘ augmentedSumReplicaCopiesEquiv q d k
    ∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧
      ∀ᶠ k : ℕ in atTop, ∀ (s : Fin (S.n * S.m)) (p : ℝ),
        let Nsq := Matrix.Transport.filteredNormSq
          ((S.actualChargeData hm hM s.val).rootPath nA (a / 2) k p) (pre k)
        let δ := ((S.actualChargeScanRound hm hM s.val nA
          (S.actualEnergyTerms Φ Ω J Δ L (fun _ => d)) a pre).meanEnergy k p - e) / gap
        0 < Nsq ∧ 0 ≤ δ ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
          4 * S' - 6 * (τ * Real.log (d : ℝ) + Real.binEntropy τ / a) -
              3 * (δ / τ) * max 0 (2 * S') - ρ k ≤
            -Real.log Nsq / (k : ℝ) := by
  classical
  intro β Xs ΩX ψ S' d a nA pre
  obtain ⟨hpre, -, hdim⟩ := hell
  have : ∀ x, Nonempty (β x) := fun _ => ⟨(0 : Fin q)⟩
  let ε : ℕ → ℝ := fun k => -2 * (Real.log (ell k).dim - (k : ℝ) * S')
  have hratio : Tendsto (fun k : ℕ => ε k / (k : ℝ)) atTop (𝓝 0) := by
    have h2 := hdim.tendsto_div_nhds_zero.const_mul (-2 : ℝ)
    rw [mul_zero] at h2
    refine h2.congr (fun k => ?_)
    change (-2 : ℝ) * ((Real.log (ell k).dim - (k : ℝ) * S') / (k : ℝ)) =
        (-2 * (Real.log (ell k).dim - (k : ℝ) * S')) / (k : ℝ)
    ring
  obtain ⟨c, Cf, hc, hCf, hbound⟩ :=
    Matrix.exists_replicaMetric_symProj_bandProduct_rough_lower_norm_three β d S.K hK
  refine ⟨fun k => ((S.K : ℝ) / 2 * (2 * |Real.log ((k : ℝ) + 1) +
      c * Real.log ((k : ℝ) + 2) + a * ε k| + Cf * Real.log ((k : ℝ) + 2) +
      2 * Real.log 2 + Real.log (3 / 2))) / (k : ℝ), ?_, ?_⟩
  · refine (Matrix.MeanTree.tendsto_rough_lower_remainder_div_nat
      ((S.K : ℝ) / 2) (1 / 2) (2 / (S.K : ℝ)) c Cf hratio).congr (fun k => ?_)
    rw [show (2 : ℝ) * (2 / (S.K : ℝ)) * ε k = a * ε k from by simp only [a]; ring]
    ring
  filter_upwards [eventually_gt_atTop 0] with k hk s p
  intro Nsq δ
  let Horizon := S.n * S.m
  let σ := CollarScan.ActualTerminals.terminalPartition S Horizon
  let Q := fun j g => receiving (σ j g) false
  let Y := fun j g => middle (σ j g)
  obtain ⟨hdisj, hnest, hfar⟩ := actualTerminal_roughLower_geometry S Horizon
  let ι₀ := addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d)
  let : DecidableEq (Config k ι₀) := Fintype.decidablePiFintype
  obtain ⟨N, ZS, hZS, hZSZS⟩ :=
    (isStarProjection_symProj
      (copyPerm ((v : ↥(Λ : Set (ℤ × ℤ)) ⊕ Bool) → Fin (nA v)) k)).exists_matrix_range_isometry
  let eA := augmentedReplicaConfigurationEquiv (V := ↥(Λ : Set (ℤ × ℤ))) q d k
  let ZO := ZS.submatrix eA (id : Fin N → Fin N)
  have hZO : ZOᴴ * ZO = 1 := by
    simpa only [ZO, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_id_id] using hZS
  have hSymm : symProj (copyPerm ((o : Option (Option ↥(Λ : Set (ℤ × ℤ)))) → ι₀ o) k) =
      (symProj (copyPerm ((v : ↥(Λ : Set (ℤ × ℤ)) ⊕ Bool) → Fin (nA v)) k)).submatrix eA eA := by
    simpa only [Matrix.reindex_apply, Equiv.symm_symm] using
      (symProj_of_intertwine eA.symm
        (φ := copyPerm ((v : ↥(Λ : Set (ℤ × ℤ)) ⊕ Bool) → Fin (nA v)) k)
        (ψ := copyPerm ((o : Option (Option ↥(Λ : Set (ℤ × ℤ)))) → ι₀ o) k)
        (fun perm x => funext fun j => rfl))
  have hZOZO : ZO * ZOᴴ =
      symProj (copyPerm ((o : Option (Option ↥(Λ : Set (ℤ × ℤ)))) → ι₀ o) k) := by
    simpa only [ZO, Matrix.conjTranspose_submatrix, Equiv.coe_refl] using
      ((Matrix.submatrix_mul_equiv ZS ZSᴴ eA (Equiv.refl (Fin N)) eA).trans
        (congrArg (fun P : Matrix (Config k (fun v => Fin (nA v)))
          (Config k (fun v => Fin (nA v))) ℂ => P.submatrix eA eA) hZSZS)).trans hSymm.symm
  have hsym : symProj (copyPerm ((v : ↥(Λ : Set (ℤ × ℤ)) ⊕ Bool) → Fin (nA v)) k) *ᵥ pre k =
      pre k :=
    symProj_mulVec_augmentedReplicaPrevector q d k Ωt (ell k)
  have hpreEq : pre k ∘ eA = replicaPrevector Ωt d k (ell k) ∘
      globalReplicaCopiesEquiv β (Fin d) (Fin d) k := by
    simp only [pre, augmentedSumReplicaCopiesEquiv, Equiv.coe_trans,
      Function.comp_assoc, eA, Equiv.symm_comp_self, Function.comp_id, β]
  let ξ : EuclideanSpace ℂ (Config k ι₀) := WithLp.toLp 2 (pre k ∘ eA)
  obtain ⟨hξne, hξnorm, _henergy, hPe, hCeq, hReq⟩ := hpre k hk
  obtain ⟨hbridgeC, hbridgeR⟩ :=
    labelProj_globalReplicaCopiesEquiv_auxiliary β (Fin d) (Fin d) k (ell k) (ell k)
  have hξ : ξ = WithLp.toLp 2 (replicaPrevector Ωt d k (ell k) ∘
      globalReplicaCopiesEquiv β (Fin d) (Fin d) k) := congrArg (WithLp.toLp 2) hpreEq
  have hC : labelProj (subsystemPerm k ι₀ {some none}) (ell k) *ᵥ ξ = ξ := by
    rw [hξ]
    exact (congrArg (fun M => M *ᵥ _) hbridgeC.symm).trans hCeq
  have hR : labelProj (subsystemPerm k ι₀ {none}) (ell k) *ᵥ ξ = ξ := by
    rw [hξ]
    exact (congrArg (fun M => M *ᵥ _) hbridgeR.symm).trans hReq
  have hsymO : symProj (copyPerm ((o : Option (Option ↥(Λ : Set (ℤ × ℤ)))) → ι₀ o) k) *ᵥ ξ =
      ξ := by
    rw [hξ]
    exact hPe
  have hle : 2 * (k : ℝ) * S' - ε k ≤ Real.log (ell k).dim + Real.log (ell k).dim :=
    le_of_eq (by
      change 2 * (k : ℝ) * S' - (-2 * (Real.log (ell k).dim - (k : ℝ) * S')) =
        Real.log (ell k).dim + Real.log (ell k).dim
      ring)
  have hKpos : (0 : ℝ) < S.K := by exact_mod_cast (show 0 < S.K by omega)
  have ht : a / 2 = 2 / (S.K : ℝ) := by
    change 4 / (S.K : ℝ) / 2 = 2 / (S.K : ℝ)
    ring
  have hthalf : 0 ≤ a / 2 := by
    rw [ht]
    positivity
  let D := S.actualChargeData hm hM s.val
  let f := CollarScan.ActualTerminals.chargeTerminalIndex S.K S.m S.M Horizon s
  let T := D.tree (Set.projIcc (0 : ℝ) 1 zero_le_one p)
  have he := hbound k N hk (∑ i, S.truncatedEnergyTerm Φ Ω J Δ L i) Ωt.ofLp e gap
    hgap hΩt hgap_pos ZO hZO hZOZO
    (CollarScan.ActualTerminals.terminalFamily S.K S.m S.M Horizon) Q Y hdisj hnest
    (T.map f) (ell k) S' (ε k) hle ξ (by rw [hξ]; exact hξne) (by rw [hξ]; exact hξnorm)
    hsymO hC hR
  simp only [MeanTree.eval_map] at he
  let A := fun j g =>
    ((replicaMetric ι₀ (2 / (S.K : ℝ)) k
        (insert (some none) ((Q (f j) g).image fun x => some (some x))))⁻¹ *
      (replicaMetric ι₀ (2 / (S.K : ℝ)) k
        (insert none (((Q (f j) g ∪ Y (f j) g)ᶜ).image fun x => some (some x))))⁻¹ *
      replicaMetric ι₀ (2 / (S.K : ℝ)) k ((Y (f j) g).image fun x => some (some x))) ^ 2
  let B := fun j g => ZOᴴ * A j g * ZO
  let M := (List.ofFn fun g : Fin S.K => T.eval (B · g)).prod
  let w := toEuclideanLin (M ^ (-(1 / 4) : ℝ)) (toEuclideanLin ZOᴴ ξ)
  let vO := toEuclideanLin ZO ((‖w‖⁻¹ : ℂ) • w)
  have hP (j : Σ _h : History S.K S.m S.M s.val, Option (ChargeChoices S.K S.M))
      (g : Fin S.K) :
      (D.leafPart j g).P.image augmentedSiteEquiv.symm =
        insert (some none) ((Q (f j) g).image fun x => some (some x)) := by
    rw [CollarScan.ActualTerminals.actualChargeData_leafPart_terminalPartition
      S hm hM Horizon s j g, augmentedPartition_eq_images]
    simp only [Finset.image_insert, Finset.image_image]
    rfl
  have hF (j : Σ _h : History S.K S.m S.M s.val, Option (ChargeChoices S.K S.M))
      (g : Fin S.K) :
      (D.leafPart j g).F.image augmentedSiteEquiv.symm =
        insert none (((Q (f j) g ∪ Y (f j) g)ᶜ).image fun x => some (some x)) := by
    rw [CollarScan.ActualTerminals.actualChargeData_leafPart_terminalPartition
      S hm hM Horizon s j g, augmentedPartition_eq_images]
    simp only [Finset.image_insert, Finset.image_image]
    change insert none ((receiving (σ (f j) g) true).image fun x => some (some x)) = _
    rw [hfar]
  have hY (j : Σ _h : History S.K S.m S.M s.val, Option (ChargeChoices S.K S.M))
      (g : Fin S.K) :
      (D.leafPart j g).Y.image augmentedSiteEquiv.symm =
        (Y (f j) g).image (fun x => some (some x)) := by
    rw [CollarScan.ActualTerminals.actualChargeData_leafPart_terminalPartition
      S hm hM Horizon s j g, augmentedPartition_eq_images]
    simp only [Finset.image_image]
    rfl
  have hroot : Nsq = ‖w‖ ^ 2 ∧
      Transport.filteredVector (D.rootPath nA (a / 2) k p) (pre k) =
        ZS *ᵥ ((‖w‖⁻¹ : ℂ) • w).ofLp := by
    have hr := (rootPath_augmented_compressed_bandProduct q d D
      (S.actualChargeData_isAdmissible hm hM s.val) hthalf k N
      (S.chargeTransportData_crossBandCommute
        (historyMeanTree S.K S.m S.M hm hM s.val)
        (fun _ => chargeChoiceTree S.K S.M hM) nA hthalf k)
      ZS hZS hZSZS (pre k) hsym p).2.2.2
    rw [ht] at hr
    simp only [Nsq, ht]
    simpa only [hP, hF, hY, T, A, B, M, w, ZO, ξ, eA,
      toEuclideanLin, toLpLin_apply, WithLp.ofLp_toLp] using! hr
  have hvO :
      Transport.filteredVector (D.rootPath nA (a / 2) k p) (pre k) ∘ eA = vO.ofLp := by
    rw [hroot.2]
    rfl
  have henergy : (S.actualChargeScanRound hm hM s.val nA
      (S.actualEnergyTerms Φ Ω J Δ L (fun _ => d)) a pre).meanEnergy k p =
      (star vO.ofLp ⬝ᵥ (globalReplicaMeanHamiltonian β (Fin d) (Fin d)
        (∑ i, S.truncatedEnergyTerm Φ Ω J Δ L i) k *ᵥ vO.ofLp)).re := by
    rw [S.actualChargeScanRound_meanEnergy_eq_globalReplicaMeanHamiltonian
      hm hM s.val Φ Ω Δ L a pre k p]
    dsimp only
    rw [hvO]
  have hδ : δ = ((star vO.ofLp ⬝ᵥ (globalReplicaMeanHamiltonian β (Fin d) (Fin d)
        (∑ i, S.truncatedEnergyTerm Φ Ω J Δ L i) k *ᵥ vO.ofLp)).re - e) / gap := by
    simp only [δ, henergy]
  obtain ⟨hw, -, hδnonneg, hlower⟩ := he
  refine ⟨hroot.1 ▸ sq_pos_of_pos (norm_pos_iff.mpr hw), hδ ▸ hδnonneg, ?_⟩
  intro τ hτ hτhalf
  rw [hroot.1, hδ]
  exact hlower τ hτ hτhalf

end OpenAI.Scan
