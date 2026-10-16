import OpenAI.Scan.SourceScan

/-!
# The leaf partitions of the collar scan

At each terminal leaf and band the physical partition of the collar scan is `X, U, Y, V`
[OAI265, §9.1, lines 83–98].
-/

namespace OpenAI.Scan

open Arealaw Matrix Filter TensorPower PermutationRepresentation SimpleGraph
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Topology

/-- A physical partition whose near side is `X ∪ U` with `X` of nonpositive depth, whose near
side lies in `A` through depth `L`, and whose middle lies in `A` at depths `1, …, L`, splits as
`X, U, Y, V` with `U ∪ Y` inside the truncation set `A ∩ {depth ≤ L}`. -/
theorem regions_of_depth_bounds {V : Type*} [Fintype V] [DecidableEq V]
    (A X : Finset V) (depth : V → ℤ) (L : ℕ) (σ : PhysicalPartition V)
    (hnear : receiving σ false = X ∪ positiveNear depth σ)
    (hX : ∀ x ∈ X, depth x ≤ 0)
    (hnearA : ∀ x, σ x = some false → x ∈ A ∧ depth x ≤ L)
    (hmid : ∀ x, σ x = none → x ∈ A ∧ depth x ∈ Finset.Icc (1 : ℤ) L) :
    receiving σ false = X ∪ positiveNear depth σ ∧
      positiveNearMiddle depth σ = positiveNear depth σ ∪ middle σ ∧
      Disjoint X (positiveNear depth σ ∪ middle σ) ∧
      Disjoint (positiveNear depth σ) (middle σ) ∧
      receiving σ true = (receiving σ false ∪ middle σ)ᶜ ∧
      positiveNear depth σ ∪ middle σ ⊆ A.filter fun x ↦ depth x ≤ L := by
  have hpos (x : V) (hx : σ x = none) : 0 < depth x := by
    have := Finset.mem_Icc.mp (hmid x hx).2; omega
  refine ⟨hnear, ?_, ?_, ?_, receiving_far_eq_compl σ, ?_⟩
  · ext x
    cases he : σ x with
    | none => simp [positiveNearMiddle, positiveNear, middle, receiving, he, hpos x he]
    | some b => cases b <;> simp [positiveNearMiddle, positiveNear, middle, receiving, he]
  · rw [Finset.disjoint_left]
    intro x hxX hx
    have h0 := hX x hxX
    rcases Finset.mem_union.mp hx with hx | hx
    · have := (Finset.mem_filter.mp hx).2; omega
    · have := hpos x (Finset.mem_filter.mp hx).2; omega
  · rw [Finset.disjoint_left]
    intro x hx hx'
    have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
    have h2 := (Finset.mem_filter.mp hx').2
    rw [h1] at h2
    exact absurd h2 (by simp)
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · have h := hnearA x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
      exact Finset.mem_filter.mpr h
    · have h := hmid x (Finset.mem_filter.mp hx).2
      exact Finset.mem_filter.mpr ⟨h.1, (Finset.mem_Icc.mp h.2).2⟩

namespace CollarScan

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
  (S : CollarScan V I)

omit [Fintype V] [Fintype I] [LinearOrder I] in
/-- A site not initially far lies in the chosen color within the band's far cutoff, hence
within depth `L` when `8Km ≤ L`. -/
theorem initialPartition_ne_far_bounds {k L : ℕ} (h : History S.K S.m S.M k) (g : Fin S.K)
    (hL : 8 * S.K * S.m ≤ L) {x : V}
    (hx : initialPartition S.A S.depth (S.lower g (h.1 g)) (S.upper g (h.1 g)) x ≠ some true) :
    x ∈ S.A ∧ S.depth x ≤ L := by
  have hoffset := (h.1 g).isLt
  have hupper : 8 * g.val * S.m + 5 * S.m + (h.1 g).val ≤ L := by
    calc
      _ ≤ 8 * g.val * S.m + 8 * S.m := by omega
      _ = 8 * (g.val + 1) * S.m := by ring
      _ ≤ 8 * S.K * S.m := Nat.mul_le_mul_right S.m (Nat.mul_le_mul_left 8 g.isLt)
      _ ≤ L := hL
  simp only [initialPartition] at hx
  by_cases hA : x ∈ S.A
  swap
  · simp [hA] at hx
  by_cases hlo : S.depth x ≤ S.lower g (h.1 g)
  · simp only [lower] at hlo
    exact ⟨hA, by omega⟩
  by_cases hhi : S.upper g (h.1 g) < S.depth x
  · simp [hA, hlo, hhi] at hx
  · simp only [upper] at hhi
    exact ⟨hA, by omega⟩

/-- Every near site of a completed history lies in the chosen color within depth `L`. -/
theorem state_near_bounds {k L : ℕ} (h : History S.K S.m S.M k) (g : Fin S.K)
    (hL : 8 * S.K * S.m ≤ L) (x : V) (hx : S.state h g x = some false) :
    x ∈ S.A ∧ S.depth x ≤ L := by
  refine S.initialPartition_ne_far_bounds h g hL fun hfar ↦ ?_
  have := S.bandState_of_initial_assigned g (h.1 g) k (fun t ↦ h.2 t g) x true hfar
  rw [state] at hx
  rw [hx] at this
  exact absurd this (by simp)

/-- Every near site before a charge lies in the chosen color within depth `L`. -/
theorem oldChargeState_near_bounds {k L : ℕ} (h : History S.K S.m S.M k) (g : Fin S.K)
    (hL : 8 * S.K * S.m ≤ L) (x : V) (hx : S.oldChargeState h g x = some false) :
    x ∈ S.A ∧ S.depth x ≤ L := by
  refine S.initialPartition_ne_far_bounds h g hL fun hfar ↦ ?_
  have := S.oldChargeState_of_initial_assigned h g hfar
  rw [hx] at this
  exact absurd this (by simp)

end CollarScan

open Classical in
/-- **The leaf partitions of the collar scan** [OAI265, §9.1, lines 83–98, and the proof of
Proposition 9.6, line 868].  At every completed or pre-charge leaf and band of the collar scan
with `8Km ≤ L`, the physical partition is `X, U, Y, V`: the near side is `X ∪ U` with
`U = positiveNear`, `UY = U ∪ Y` is the positive-depth part of near side and middle, `X`, `U`,
`Y` are disjoint, `V` is the complement of `XUY`, and `U ∪ Y ⊆ S₀ = A ∩ T_L`. -/
theorem sourceScan_terminal_regions (X : ScannerExponents) (Ctr : ℝ) (R : ℕ)
    (Λ A T : Finset (ℤ × ℤ)) [LinearOrder (supports Λ R)] (hT : T.Nonempty) (n : ℕ)
    (hKL : 8 * X.K n * X.m n ≤ X.L n) :
    let S := sourceScan X Ctr R Λ A T hT n
    let Xs := S.A.filter fun x => x.val ∈ T
    ∀ (j : CollarScan.ActualTerminals.terminalFamily S.K S.m S.M (S.n * S.m)) (g : Fin S.K),
      let σ := CollarScan.ActualTerminals.terminalPartition S (S.n * S.m) j g
      receiving σ false = Xs ∪ positiveNear S.depth σ ∧
      positiveNearMiddle S.depth σ = positiveNear S.depth σ ∪ middle σ ∧
      Disjoint Xs (positiveNear S.depth σ ∪ middle σ) ∧
      Disjoint (positiveNear S.depth σ) (middle σ) ∧
      receiving σ true = (receiving σ false ∪ middle σ)ᶜ ∧
      positiveNear S.depth σ ∪ middle σ ⊆ S.truncationSet (X.L n) := by
  intro S Xs j g σ
  have hdepth : S.depth = fun x ↦ ambientDepth T hT x.val := rfl
  have hL : 8 * S.K * S.m ≤ X.L n := hKL
  have hX : ∀ x ∈ Xs, S.depth x ≤ 0 := fun x hx ↦
    (ambientDepth_le_iff_mem_dilation T hT x.val 0).mpr
      (by simpa only [ambientDilation_zero] using (Finset.mem_filter.mp hx).2)
  refine regions_of_depth_bounds S.A Xs S.depth (X.L n) σ ?_ hX ?_ ?_
  · rcases j with ⟨_, h⟩ | ⟨_, h⟩
    · exact (S.state_receiving_regions hT hdepth h g).1
    · exact (S.oldChargeState_receiving_regions hT hdepth h g).1
  · rcases j with ⟨_, h⟩ | ⟨_, h⟩
    · exact S.state_near_bounds h g hL
    · exact S.oldChargeState_near_bounds h g hL
  · rcases j with ⟨_, h⟩ | ⟨_, h⟩
    · intro x hx
      exact ⟨(initial_middle_depth S.A S.depth _ _
        (S.bandState_unassigned g (h.1 g) _ (fun t ↦ h.2 t g) x hx).1 false).1,
        S.state_depth_bounds h g hL x hx⟩
    · intro x hx
      exact ⟨(initial_middle_depth S.A S.depth _ _
        (S.oldChargeState_initial_none h g x hx) false).1,
        S.oldChargeState_depth_bounds h g hL x hx⟩

end OpenAI.Scan
