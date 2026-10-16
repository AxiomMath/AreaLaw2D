/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 74ecad48c409da176dc3e49ccd2bd9dd0462c9d9,
`TNLean/PEPS/AreaLaw/Scan/ActualTransportEstimates.lean` (Apache 2.0).
Namespace `TNLean.PEPS.AreaLaw.Scan` renamed to `OpenAI.Scan`. Adapted to this project's
domain encoding: TNLean's `Site Λ` and `domainGraph Λ` are `↥(Λ : Set (ℤ × ℤ))` and
`(hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ))`, and `Geometry.boundaryEndpoints Λ S.A` is
`OpenAI.cutEndpoints Λ (S.A.map (Function.Embedding.subtype _))`, as in
`OpenAI.Scan.SupportLocalization`. The `_domainGraph` declaration names are kept.
TNLean's bundled `LocalHamiltonian Λ q R J` is an interaction `Φ` with
`hΦ : OpenAI.IsAdmissible Λ R J Φ`, its state space `StateSpace Λ q` is
`EuclideanSpace ℂ (Reg (Qudits q) Λ)`, and the labels `AdmissibleSupport Λ R` are
`↥(supports Λ R)`, as in `OpenAI.Scan.ActualEnergyTerms`.
-/
import OpenAI.Scan.ActualChargeData
import OpenAI.Scan.ActualEnergyTerms
import OpenAI.Scan.FillSupportCompatibility
import OpenAI.Scan.TransportDimension
import OpenAI.ReplicaTransport

/-!
# Entropy and energy transport for the actual fill and charge rounds

The four conclusions of Proposition 7.4 apply to the actual recursive history
and conditional-choice trees and to the actual augmented truncated Hamiltonian.
Admissibility, positive supported contractions, support compatibility,
cross-band commutation and logarithmic dimensions are derived from the existing
constructions. The physical logarithmic cap is independent of both auxiliary sizes.

Universal constants precede all physical data. After the data and interpolation
scale are fixed, one logarithmic-error sequence and one vanishing-remainder
sequence work for every replica count. Their bounds are independent of the
supplied nonzero symmetric vector, interpolation parameter and energy eigenvalue.
Only the energy clause assumes that the supplied vector is an eigenvector of
the actual augmented truncated replica Hamiltonian.

No physical pre-vector, ground state of the truncated Hamiltonian, comparator,
or complete scanner data is constructed here.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
Proposition 7.4, `06-transport.tex`, lines 377–434, and the actual scanner
construction in `08-scanner.tex`, at `openai/math@adc7f124`.
-/

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Set Filter Topology MeasureTheory PermutationRepresentation Entropy

noncomputable section

namespace OpenAI.Scan.CollarScan

open Arealaw SimpleGraph TensorPower TensorPower.ReplicaTransport

/-- The actual fill round satisfies all four conclusions of Proposition 7.4.
The energy equation is for the actual truncated Hamiltonian, while the derivative,
entropy and endpoint-inclusive integral require only a supplied nonzero symmetric vector. -/
theorem actualFill_transport_domainGraph :
    ∃ c₀ Cent eent Cen een : ℝ, 0 < c₀ ∧
      ∀ {Λ T : Finset (ℤ × ℤ)} {q R : ℕ} {J Δ : ℝ}
        [NeZero q] [LinearOrder (supports Λ R)]
        (aux : Bool → ℕ) [∀ b, NeZero (aux b)]
        (Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) ℂ)
        (hΦ : IsAdmissible Λ R J Φ) (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ))
        (S : CollarScan (↥(Λ : Set (ℤ × ℤ))) (supports Λ R)) (hT : T.Nonempty),
        S.graph = (hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ)) →
        S.depth = (fun x => ambientDepth T hT x.val) →
        (∀ i, (S.anchor i).1 ∈ i.val) → 0 < Δ → ‖Ω‖ = 1 →
        ∀ {s L : ℕ} (hn : 0 < S.n), s + 1 ≤ S.n * S.m → S.r₀ ≤ S.D →
        ∀ (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m),
        8 * S.K * S.m ≤ L → ∀ (hC : 0 < S.C₁),
        (∀ d : ℕ, 1 ≤ d → d ≤ L →
          (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
        (∀ t ∈ T, ∀ z ∈ cutEndpoints Λ (S.A.map (Function.Embedding.subtype _)),
          ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) →
        ∀ {a : ℝ}, 0 < a → a * transportLogDimBound q S.r₀ ≤ c₀ →
        let hm : 0 < S.m := by omega
        let hM : 0 < S.M := chargeSlotCount_pos hC (Nat.succ_le_iff.mpr hn) hDpos
        let n := augmentedDimensions (V := ↥(Λ : Set (ℤ × ℤ))) q aux
        let D := S.actualFillData hm hM s
        let E := S.actualEnergyTerms Φ Ω J Δ L aux
        let ℓ := transportLogDimBound q S.r₀
        let Hbar := fun r => copyMean n r
          (augmentOperator q aux (∑ i, S.truncatedEnergyTerm Φ Ω J Δ L i))
        ∃ β ε : ℕ → ℝ, (β =O[atTop] fun r : ℕ => Real.log (r + 1)) ∧
          Tendsto ε atTop (𝓝 0) ∧
          ∀ (r : ℕ) (pre : Config r (fun v => Fin (n v)) → ℂ),
            pre ∈ symmetricSubspace r (fun v => Fin (n v)) → pre ≠ 0 →
            (∀ p ∈ Ioo (0 : ℝ) 1,
              HasDerivAt
                (fun p' => -Real.log (Transport.filteredNormSq (D.rootPath n (a / 2) r p') pre))
                (D.exactDerivative n (a / 2) r pre p) p ∧
              (r : ℝ) * a * D.entropyGain n (a / 2) r pre p -
                  Cent * r * a * S.K * a ^ (1 / 4 : ℝ) * ℓ ^ eent - β r ≤
                D.exactDerivative n (a / 2) r pre p ∧
              ∀ E₀ : ℝ, Hbar r *ᵥ pre = (E₀ : ℂ) • pre →
                let v := Transport.filteredVector (D.rootPath n (a / 2) r p) pre
                (star v ⬝ᵥ (Hbar r *ᵥ v)).re ≤
                  2 * E₀ + Cen * a ^ 2 * ℓ ^ een * D.energyError E (a / 2) r pre p + ε r) ∧
            ∀ p₀ p₁ : ℝ, 0 ≤ p₀ → p₀ ≤ p₁ → p₁ ≤ 1 →
              ∫ p in p₀..p₁, ((r : ℝ) * a * D.entropyGain n (a / 2) r pre p -
                  Cent * r * a * S.K * a ^ (1 / 4 : ℝ) * ℓ ^ eent - β r) ≤
                Real.log (Transport.filteredNormSq (D.rootPath n (a / 2) r p₀) pre) -
                  Real.log (Transport.filteredNormSq (D.rootPath n (a / 2) r p₁) pre) := by
  classical
  obtain ⟨c₀, Cent, eent, Cen, een, hc₀, htransport⟩ := transport
  refine ⟨c₀, Cent, eent, Cen, een, hc₀, ?_⟩
  intro Λ T q R J Δ _ _ aux _ Φ hΦ Ω S hT hgraph hdepth hanchor hΔ hΩ
    s L hn hs hr hDpos hD hL hC hrows hclear a ha haℓ
  let hm : 0 < S.m := by omega
  let hM : 0 < S.M := chargeSlotCount_pos hC (Nat.succ_le_iff.mpr hn) hDpos
  let n := augmentedDimensions (V := ↥(Λ : Set (ℤ × ℤ))) q aux
  let D := S.actualFillData hm hM s
  let E := S.actualEnergyTerms Φ Ω J Δ L aux
  let Hbar := fun r => copyMean n r
    (augmentOperator q aux (∑ i, S.truncatedEnergyTerm Φ Ω J Δ L i))
  have hq : 1 ≤ q := NeZero.pos q
  have hE := S.actualEnergyTerms_spec Φ Ω hΦ hgraph hanchor hΔ hΩ L aux
  have hcompat : D.SupportCompatible E :=
    S.fillTransportData_supportCompatible_domainGraph hT hgraph hdepth
      (historyMeanTree S.K S.m S.M hm hM s)
      hn hs hr hDpos hD hL hrows hclear n E (fun _ => rfl)
  have ht : 0 ≤ a / 2 := (half_pos ha).le
  have hcomm : ∀ r, D.CrossBandCommute n (a / 2) r := fun r =>
    S.fillTransportData_crossBandCommute
      (historyMeanTree S.K S.m S.M hm hM s) n ht r
  have hmove : ∀ hist c g, logDim n (D.move hist c g).subsystem ≤
      transportLogDimBound q S.r₀ :=
    S.fillTransportData_logDim_move_le
      (historyMeanTree S.K S.m S.M hm hM s) n hq (fun _ => rfl)
  have hsplit : ∀ i, (D.splitLeaves E i).Nonempty →
      logDim n (E.support i) ≤ transportLogDimBound q S.r₀ :=
    S.fillTransportData_logDim_support_le_domainGraph hgraph
      (historyMeanTree S.K S.m S.M hm hM s)
      n hq (fun _ => rfl) hL E (fun _ => rfl)
  obtain ⟨β, ε, hβ, hε, hresult⟩ := htransport n D E
    (S.actualFillData_isAdmissible hm hM s) hE.1 hE.2.1 hE.2.2 hcompat
    ha (one_le_transportLogDimBound hq S.r₀) haℓ hcomm hmove hsplit
  have henergy (r : ℕ) : E.replicaEnergy r = Hbar r :=
    S.replicaEnergy_actualEnergyTerms Φ Ω J Δ L aux r
  refine ⟨β, ε, hβ, hε, fun r pre hpre hne ↦ ?_⟩
  obtain ⟨hpoint, hintegral⟩ := hresult r pre hpre hne
  refine ⟨fun p hp ↦ ?_, hintegral⟩
  obtain ⟨hderiv, hent, hen⟩ := hpoint p hp
  exact ⟨hderiv, hent, fun E₀ heig ↦ by simpa only [henergy r] using hen E₀ (henergy r ▸ heig)⟩

/-- The actual charge round satisfies all four conclusions of Proposition 7.4.
The energy equation is for the actual truncated Hamiltonian, while the derivative,
entropy and endpoint-inclusive integral require only a supplied nonzero symmetric vector. -/
theorem actualCharge_transport_domainGraph :
    ∃ c₀ Cent eent Cen een : ℝ, 0 < c₀ ∧
      ∀ {Λ T : Finset (ℤ × ℤ)} {q R : ℕ} {J Δ : ℝ}
        [NeZero q] [LinearOrder (supports Λ R)]
        (aux : Bool → ℕ) [∀ b, NeZero (aux b)]
        (Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (Qudits q) X) (Reg (Qudits q) X) ℂ)
        (hΦ : IsAdmissible Λ R J Φ) (Ω : EuclideanSpace ℂ (Reg (Qudits q) Λ))
        (S : CollarScan (↥(Λ : Set (ℤ × ℤ))) (supports Λ R)) (hT : T.Nonempty),
        S.graph = (hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ)) →
        S.depth = (fun x => ambientDepth T hT x.val) →
        (∀ i, (S.anchor i).1 ∈ i.val) → 0 < Δ → ‖Ω‖ = 1 →
        ∀ {s L : ℕ} (hn : 0 < S.n), s + 1 ≤ S.n * S.m → S.r₀ ≤ S.D →
        ∀ (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m),
        8 * S.K * S.m ≤ L → ∀ (hC : 0 < S.C₁),
        (∀ d : ℕ, 1 ≤ d → d ≤ L →
          (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
        (∀ t ∈ T, ∀ z ∈ cutEndpoints Λ (S.A.map (Function.Embedding.subtype _)),
          ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) →
        ∀ {a : ℝ}, 0 < a → a * transportLogDimBound q S.r₀ ≤ c₀ →
        let hm : 0 < S.m := by omega
        let hM : 0 < S.M := chargeSlotCount_pos hC (Nat.succ_le_iff.mpr hn) hDpos
        let n := augmentedDimensions (V := ↥(Λ : Set (ℤ × ℤ))) q aux
        let D := S.actualChargeData hm hM s
        let E := S.actualEnergyTerms Φ Ω J Δ L aux
        let ℓ := transportLogDimBound q S.r₀
        let Hbar := fun r => copyMean n r
          (augmentOperator q aux (∑ i, S.truncatedEnergyTerm Φ Ω J Δ L i))
        ∃ β ε : ℕ → ℝ, (β =O[atTop] fun r : ℕ => Real.log (r + 1)) ∧
          Tendsto ε atTop (𝓝 0) ∧
          ∀ (r : ℕ) (pre : Config r (fun v => Fin (n v)) → ℂ),
            pre ∈ symmetricSubspace r (fun v => Fin (n v)) → pre ≠ 0 →
            (∀ p ∈ Ioo (0 : ℝ) 1,
              HasDerivAt
                (fun p' => -Real.log (Transport.filteredNormSq (D.rootPath n (a / 2) r p') pre))
                (D.exactDerivative n (a / 2) r pre p) p ∧
              (r : ℝ) * a * D.entropyGain n (a / 2) r pre p -
                  Cent * r * a * S.K * a ^ (1 / 4 : ℝ) * ℓ ^ eent - β r ≤
                D.exactDerivative n (a / 2) r pre p ∧
              ∀ E₀ : ℝ, Hbar r *ᵥ pre = (E₀ : ℂ) • pre →
                let v := Transport.filteredVector (D.rootPath n (a / 2) r p) pre
                (star v ⬝ᵥ (Hbar r *ᵥ v)).re ≤
                  2 * E₀ + Cen * a ^ 2 * ℓ ^ een * D.energyError E (a / 2) r pre p + ε r) ∧
            ∀ p₀ p₁ : ℝ, 0 ≤ p₀ → p₀ ≤ p₁ → p₁ ≤ 1 →
              ∫ p in p₀..p₁, ((r : ℝ) * a * D.entropyGain n (a / 2) r pre p -
                  Cent * r * a * S.K * a ^ (1 / 4 : ℝ) * ℓ ^ eent - β r) ≤
                Real.log (Transport.filteredNormSq (D.rootPath n (a / 2) r p₀) pre) -
                  Real.log (Transport.filteredNormSq (D.rootPath n (a / 2) r p₁) pre) := by
  classical
  obtain ⟨c₀, Cent, eent, Cen, een, hc₀, htransport⟩ := transport
  refine ⟨c₀, Cent, eent, Cen, een, hc₀, ?_⟩
  intro Λ T q R J Δ _ _ aux _ Φ hΦ Ω S hT hgraph hdepth hanchor hΔ hΩ
    s L hn hs hr hDpos hD hL hC hrows hclear a ha haℓ
  let hm : 0 < S.m := by omega
  let hM : 0 < S.M := chargeSlotCount_pos hC (Nat.succ_le_iff.mpr hn) hDpos
  let n := augmentedDimensions (V := ↥(Λ : Set (ℤ × ℤ))) q aux
  let D := S.actualChargeData hm hM s
  let E := S.actualEnergyTerms Φ Ω J Δ L aux
  let Hbar := fun r => copyMean n r
    (augmentOperator q aux (∑ i, S.truncatedEnergyTerm Φ Ω J Δ L i))
  have hq : 1 ≤ q := NeZero.pos q
  have hE := S.actualEnergyTerms_spec Φ Ω hΦ hgraph hanchor hΔ hΩ L aux
  have hcompat : D.SupportCompatible E :=
    S.chargeTransportData_supportCompatible_domainGraph hT hgraph hdepth
      (historyMeanTree S.K S.m S.M hm hM s)
      (fun _ => chargeChoiceTree S.K S.M hM)
      hn hs hr hDpos hD hL hrows hclear n E (fun _ => rfl)
  have ht : 0 ≤ a / 2 := (half_pos ha).le
  have hcomm : ∀ r, D.CrossBandCommute n (a / 2) r := fun r =>
    S.chargeTransportData_crossBandCommute
      (historyMeanTree S.K S.m S.M hm hM s)
      (fun _ => chargeChoiceTree S.K S.M hM) n ht r
  have hmove : ∀ hist c g, logDim n (D.move hist c g).subsystem ≤
      transportLogDimBound q S.r₀ :=
    S.chargeTransportData_logDim_move_le_domainGraph hgraph
      (historyMeanTree S.K S.m S.M hm hM s)
      (fun _ => chargeChoiceTree S.K S.M hM) n hq (fun _ => rfl)
  have hsplit : ∀ i, (D.splitLeaves E i).Nonempty →
      logDim n (E.support i) ≤ transportLogDimBound q S.r₀ :=
    S.chargeTransportData_logDim_support_le_domainGraph hgraph
      (historyMeanTree S.K S.m S.M hm hM s)
      (fun _ => chargeChoiceTree S.K S.M hM)
      n hq (fun _ => rfl) hL E (fun _ => rfl)
  obtain ⟨β, ε, hβ, hε, hresult⟩ := htransport n D E
    (S.actualChargeData_isAdmissible hm hM s) hE.1 hE.2.1 hE.2.2 hcompat
    ha (one_le_transportLogDimBound hq S.r₀) haℓ hcomm hmove hsplit
  have henergy (r : ℕ) : E.replicaEnergy r = Hbar r :=
    S.replicaEnergy_actualEnergyTerms Φ Ω J Δ L aux r
  refine ⟨β, ε, hβ, hε, fun r pre hpre hne ↦ ?_⟩
  obtain ⟨hpoint, hintegral⟩ := hresult r pre hpre hne
  refine ⟨fun p hp ↦ ?_, hintegral⟩
  obtain ⟨hderiv, hent, hen⟩ := hpoint p hp
  exact ⟨hderiv, hent, fun E₀ heig ↦ by simpa only [henergy r] using hen E₀ (henergy r ▸ heig)⟩

end OpenAI.Scan.CollarScan
