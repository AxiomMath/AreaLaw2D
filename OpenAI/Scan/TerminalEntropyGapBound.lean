import OpenAI.FiniteProductEntropyBounds
import OpenAI.Scan.ActualTerminalPartitions
import OpenAI.Scan.PrefixApproximation
import OpenAI.Scan.FrontPrefixFamily
import OpenAI.Scan.ReceivingRegions

/-!
# A uniform bound on the pre-comparison entropy gap

At each terminal leaf of the collar scan, with physical partition `X, U, Y, V`, the entropy
gap `g_pre = S(XU) + S(V) - S(Y)` of the sharp comparisons of [OAI265, Proposition 8.1] is at
most `2 S(X) + 2 B_sh + 6 n D log q`, where `B_sh` bounds the entropy of every positive-depth
prefix.  Indeed `S(XU) ≤ S(X) + S(U)` and, by purity, `S(V) = S(XUY) ≤ S(X) + S(UY)`; the
regions `U` and `UY` lie within `3 n D` sites of nested whole-row prefixes, which costs at most
`3 n D log q` each by subadditivity and Araki–Lieb [OAI265, proof of Proposition 9.6,
lines 870–877].

## Main statements

* `FiniteProduct.entropy_union_add_entropy_compl_sub_le`: the entropy inequality for one
  partition with prefix approximations.
* `OpenAI.Scan.CollarScan.terminalPartition_entropyGap_le`: the bound at every terminal leaf.
-/

open scoped BigOperators symmDiff
open SimpleGraph

namespace FiniteProduct

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- For a region `X` disjoint from `W`, a subregion `U ⊆ W`, and regions `D ⊆ U`, `W ⊆ D'`
whose differences have at most `c` sites and whose entropies are at most `B`, the gap
`S(X ∪ U) + S((X ∪ W)ᶜ) - S(Y)` is at most `2 S(X) + 2 B + 2 c log q`. -/
theorem entropy_union_add_entropy_compl_sub_le (q : ℕ) (ψ : EuclideanSpace ℂ (V → Fin q))
    (hψ : ‖ψ‖ = 1) {X U W Y D D' : Finset V} {B : ℝ} {c : ℕ}
    (hXW : Disjoint X W) (hUW : U ⊆ W) (hD : D ⊆ U) (hD' : W ⊆ D')
    (hDc : (U \ D).card ≤ c) (hD'c : (D' \ W).card ≤ c)
    (hDB : entropy (fun _ : V => Fin q) ψ D ≤ B) (hD'B : entropy (fun _ : V => Fin q) ψ D' ≤ B) :
    entropy (fun _ : V => Fin q) ψ (X ∪ U) + entropy (fun _ : V => Fin q) ψ (X ∪ W)ᶜ -
        entropy (fun _ : V => Fin q) ψ Y ≤
      2 * entropy (fun _ : V => Fin q) ψ X + 2 * B + 2 * c * Real.log q := by
  set β := fun _ : V => Fin q
  have hlogq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hcard (R : Finset V) (hR : R.card ≤ c) : entropy β ψ R ≤ c * Real.log q :=
    (entropy_le_card_mul_log q ψ hψ R).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hR) hlogq)
  have hXU : entropy β ψ (X ∪ U) ≤ entropy β ψ X + entropy β ψ U :=
    entropy_union_le β ψ hψ X U (Finset.disjoint_of_subset_right hUW hXW)
  have hXW' : entropy β ψ (X ∪ W) ≤ entropy β ψ X + entropy β ψ W :=
    entropy_union_le β ψ hψ X W hXW
  have hU : entropy β ψ U ≤ entropy β ψ D + entropy β ψ (U \ D) :=
    entropy_le_entropy_add_sdiff β ψ hψ hD
  have hW : entropy β ψ W ≤ entropy β ψ D' + entropy β ψ (D' \ W) :=
    entropy_le_entropy_sdiff_add β ψ hψ hD'
  have hY := entropy_nonneg β ψ hψ Y
  rw [entropy_compl]
  linarith [hcard _ hDc, hcard _ hD'c]

end FiniteProduct

namespace OpenAI.Scan.CollarScan

open ActualTerminals

variable {I : Type} [Fintype I] [LinearOrder I]

open Classical in
/-- **The uniform bound on `g_pre`** [OAI265, proof of Proposition 9.6, lines 870–877]: at
every terminal leaf of a lattice collar scan, `S(XU) + S(V) - S(Y) ≤ 2 S(X) + 2 B_sh +
6 n D log q`, where `B_sh` bounds the entropies of the positive-depth prefixes of depth at
most `L`. -/
theorem terminalPartition_entropyGap_le {q : ℕ}
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (↥(Λ : Set (ℤ × ℤ))) I)
    (hgraph : S.graph = (hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ)))
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    (hn : 0 < S.n) (hr : S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m)
    {L : ℕ} (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ j : ℕ, 1 ≤ j → j ≤ L →
      (ambientDilation T j \ ambientDilation T (j - 1)).card ≤ S.n)
    (Ωt : EuclideanSpace ℂ (↥(Λ : Set (ℤ × ℤ)) → Fin q)) (hΩt : ‖Ωt‖ = 1) {Bsh : ℝ}
    (hsh : ∀ j : Fin (L + 1),
      FiniteProduct.entropy (fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q) Ωt
        (positiveDepthPrefix S.A S.depth (j.val : ℤ)) ≤ Bsh)
    (j : terminalFamily S.K S.m S.M (S.n * S.m)) (g : Fin S.K) :
    let ent := FiniteProduct.entropy (fun _ : ↥(Λ : Set (ℤ × ℤ)) ↦ Fin q) Ωt
    let σ := terminalPartition S (S.n * S.m) j g
    ent (receiving σ false) + ent (receiving σ false ∪ middle σ)ᶜ - ent (middle σ) ≤
      2 * ent (S.A.filter fun x ↦ x.val ∈ T) + 2 * Bsh +
        2 * ((3 * S.n * S.D : ℕ) : ℝ) * Real.log q := by
  intro ent σ
  set X := S.A.filter fun x ↦ x.val ∈ T with hX
  -- the regions of the leaf and their prefix approximations
  obtain ⟨hreg, Dn, hDn, Df, hDf, hnear, hfar, hnearCard, hfarCard⟩ :
      (receiving σ false = X ∪ positiveNear S.depth σ ∧
        receiving σ false ∪ middle σ = X ∪ positiveNearMiddle S.depth σ) ∧
      ∃ Dn ∈ Set.range fun i : Fin (L + 1) ↦ positiveDepthPrefix S.A S.depth (i.val : ℤ),
      ∃ Df ∈ Set.range fun i : Fin (L + 1) ↦ positiveDepthPrefix S.A S.depth (i.val : ℤ),
        Dn ⊆ positiveNear S.depth σ ∧ positiveNearMiddle S.depth σ ⊆ Df ∧
        (positiveNear S.depth σ ∆ Dn).card ≤ 3 * S.n * S.D ∧
        (positiveNearMiddle S.depth σ ∆ Df).card ≤ 3 * S.n * S.D := by
    rcases j with ⟨r, h⟩ | ⟨r, h⟩
    · obtain ⟨h1, h2, -⟩ := state_receiving_regions hT S hdepth h g
      obtain ⟨hnear, hfar, _, _, hnearCard, hfarCard⟩ :=
        S.state_prefix_approximation_domainGraph hT hgraph hdepth h g hn
          (Nat.le_of_lt_succ r.isLt) hr hDpos hD hL hrows
      have hmem := S.front_positiveDepthPrefix_mem_fixed_family hn hL g (h.1 g) r.val
        (Nat.le_of_lt_succ r.isLt)
      exact ⟨⟨h1, h2⟩, _, hmem.1, _, hmem.2, hnear, hfar, hnearCard, hfarCard⟩
    · obtain ⟨h1, h2, -⟩ := oldChargeState_receiving_regions hT S hdepth h g
      obtain ⟨hnear, hfar, _, _, hnearCard, hfarCard⟩ :=
        S.oldChargeState_prefix_approximation_domainGraph hT hgraph hdepth h g hn
          (Nat.succ_le_of_lt r.isLt) hr hDpos hD hL hrows
      have hmem := S.front_positiveDepthPrefix_mem_fixed_family hn hL g (h.1 g) (r.val + 1)
        (Nat.succ_le_of_lt r.isLt)
      exact ⟨⟨h1, h2⟩, _, hmem.1, _, hmem.2, hnear, hfar, hnearCard, hfarCard⟩
  obtain ⟨i, rfl⟩ := hDn
  obtain ⟨i', rfl⟩ := hDf
  have hdepthX : ∀ x ∈ X, S.depth x ≤ 0 := fun x hx ↦ by
    simpa only [hdepth, Nat.cast_zero] using
      (ambientDepth_le_iff_mem_dilation T hT x.val 0).mpr
        ((ambientDilation_zero T).symm ▸ (Finset.mem_filter.mp hx).2)
  have hXW : Disjoint X (positiveNearMiddle S.depth σ) :=
    Finset.disjoint_left.mpr fun x hx hx' ↦
      (not_lt_of_ge (hdepthX x hx)) (Finset.mem_filter.mp hx').2
  have hUW : positiveNear S.depth σ ⊆ positiveNearMiddle S.depth σ :=
    Finset.filter_subset_filter _ Finset.subset_union_left
  have hsd (A B : Finset ↥(Λ : Set (ℤ × ℤ))) : (A \ B).card ≤ (A ∆ B).card :=
    Finset.card_le_card fun x hx ↦ Finset.mem_symmDiff.mpr (Or.inl (Finset.mem_sdiff.mp hx))
  have hsd' (A B : Finset ↥(Λ : Set (ℤ × ℤ))) : (B \ A).card ≤ (A ∆ B).card :=
    Finset.card_le_card fun x hx ↦ Finset.mem_symmDiff.mpr (Or.inr (Finset.mem_sdiff.mp hx))
  rw [hreg.2, hreg.1]
  exact FiniteProduct.entropy_union_add_entropy_compl_sub_le q Ωt hΩt hXW hUW hnear hfar
    ((hsd _ _).trans hnearCard) ((hsd' _ _).trans hfarCard) (hsh i) (hsh i')

end OpenAI.Scan.CollarScan
