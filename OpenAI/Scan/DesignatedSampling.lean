/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Ported from LionSR/TNLean commit 74ecad48c409da176dc3e49ccd2bd9dd0462c9d9,
`TNLean/PEPS/AreaLaw/Scan/DesignatedSampling.lean` (Apache 2.0).
Namespace `TNLean.PEPS.AreaLaw.Scan` renamed to `OpenAI.Scan`. Adapted to this project's
domain encoding: TNLean's `Site Λ` and `domainGraph Λ` are `↥(Λ : Set (ℤ × ℤ))` and
`(hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ))`, and `Geometry.boundaryEndpoints Λ S.A` is
`OpenAI.cutEndpoints Λ (S.A.map (Function.Embedding.subtype _))`, as in
`OpenAI.Scan.SupportLocalization`. The `_domainGraph` declaration names are kept.
TNLean's `setDist`, `designatedSupport`, `crossingLabels` and
`truncationRadius_eq_of_mem_crossingLabels` of a general finite graph
(`TNLean/PEPS/AreaLaw/FiniteSetTruncation.lean` and `CrossingBudget.lean`) are ported here into
`OpenAI.Scan`, `graphBall` and `componentFinset` written out as filters; the repository's
versions of the same names in `OpenAI` are their specialization to the induced square lattice,
and `map_designatedSupport_domainGraph` identifies the two.
-/
import OpenAI.Scan.ExpectedMoveCost
import OpenAI.CrossingBudget

/-!
# Actual sampling of the truncated designated supports

The original compact truncation set is the chosen color inside the depth-L
collar. The actual old middle lies in this set. A designated support crossing
that middle therefore equals the fixed-radius charge ball by the established
variable-radius truncation theorem. This identifies the selected move with the
unassigned part of the designated support, rather than assuming that every
truncated support has the base radius.

The designated support of a label in a general finite graph is defined here; on the induced
square-lattice graph of `Λ` it is the repository's `OpenAI.designatedSupport`
(`map_designatedSupport_domainGraph`).

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 225–233 and 331–337, at `openai/math@adc7f124`.
-/

namespace OpenAI.Scan

open scoped BigOperators
open SimpleGraph

/-! ### Designated supports in a finite graph -/

section GraphSupports

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The graph distance `d_G(x, S₀) = min_{y ∈ S₀} d_G(x, y)`, infinite when `x` cannot reach
`S₀` (`03-quasilocal.tex`, line 418). -/
noncomputable def setDist (G : SimpleGraph ι) (S₀ : Finset ι) (x : ι) : ℕ∞ :=
  S₀.inf fun y => G.edist x y

/-- **The designated support** after truncation (`eq:quasilocal-variable-radius`,
`03-quasilocal.tex`, lines 417–424): `N_r(a)` with `r = max {r₀, ⌊d/2⌋}` when
`d = d_G(a, S₀) < ∞`, and the connected component of `a` otherwise. -/
noncomputable def designatedSupport (G : SimpleGraph ι) (S₀ : Finset ι) (r₀ : ℕ) (a : ι) :
    Finset ι := by
  classical
  exact if setDist G S₀ a = ⊤ then Finset.univ.filter fun x => G.Reachable a x
  else Finset.univ.filter fun x => G.edist a x ≤ truncationRadius r₀ (setDist G S₀ a).toNat

/-- The labels whose designated support meets both `X` and its complement
(`03-quasilocal.tex`, lines 436–438). -/
noncomputable def crossingLabels {κ : Type*} [Fintype κ] (G : SimpleGraph ι) (S₀ : Finset ι)
    (r₀ : ℕ) (a : κ → ι) (X : Finset ι) : Finset κ := by
  classical
  exact Finset.univ.filter fun i =>
    (∃ x ∈ designatedSupport G S₀ r₀ (a i), x ∈ X) ∧
      ∃ x ∈ designatedSupport G S₀ r₀ (a i), x ∉ X

/-- **Crossing supports have radius `r₀`** (`03-quasilocal.tex`, lines 439–440 and
507–510): if the designated support of a label meets `X ⊆ S₀` and its complement, the
anchor has finite distance from `S₀` and its truncation radius is `r₀`. -/
theorem truncationRadius_eq_of_mem_crossingLabels {κ : Type*} [Fintype κ]
    {G : SimpleGraph ι} {S₀ : Finset ι} {r₀ : ℕ} {a : κ → ι} {X : Finset ι} (hX : X ⊆ S₀)
    {i : κ} (hi : i ∈ crossingLabels G S₀ r₀ a X) :
    setDist G S₀ (a i) ≠ ⊤ ∧ truncationRadius r₀ (setDist G S₀ (a i)).toNat = r₀ ∧
      designatedSupport G S₀ r₀ (a i) =
        Finset.univ.filter fun x => G.edist (a i) x ≤ r₀ := by
  classical
  simp only [crossingLabels, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  obtain ⟨⟨x, hxD, hxX⟩, -⟩ := hi
  have hfin : setDist G S₀ (a i) ≠ ⊤ := by
    intro htop
    simp only [designatedSupport, htop, ite_true, Finset.mem_filter,
      Finset.mem_univ, true_and] at hxD
    have : setDist G S₀ (a i) ≤ G.edist (a i) x := Finset.inf_le (hX hxX)
    rw [htop, top_le_iff] at this
    exact SimpleGraph.edist_ne_top_iff_reachable.mpr hxD this
  set d := (setDist G S₀ (a i)).toNat with hd
  have hdcoe : (d : ℕ∞) = setDist G S₀ (a i) := ENat.natCast_toNat hfin
  simp only [designatedSupport, hfin, ite_false, Finset.mem_filter, Finset.mem_univ,
    true_and] at hxD
  have hdle : (d : ℕ∞) ≤ G.edist (a i) x := by rw [hdcoe]; exact Finset.inf_le (hX hxX)
  have hr : truncationRadius r₀ d = r₀ := by
    refine max_eq_left (not_lt.mp fun hlt ↦ ?_)
    have h' : G.edist (a i) x ≤ ((max r₀ (d / 2) : ℕ) : ℕ∞) := hxD
    rw [max_eq_right hlt.le] at h'
    have : d ≤ d / 2 := by exact_mod_cast hdle.trans h'
    omega
  refine ⟨hfin, hr, ?_⟩
  simp only [designatedSupport, hfin, ite_false, ← hd, hr]

end GraphSupports

section DomainGraph

variable {Λ : Finset (ℤ × ℤ)}

/-- On the induced square-lattice graph, the distance to a set of sites is the domain
distance to the same set read in `ℤ²`. -/
theorem setDist_domainGraph (S₀ : Finset ↥(Λ : Set (ℤ × ℤ))) (a : ↥(Λ : Set (ℤ × ℤ))) :
    setDist ((hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ))) S₀ a =
      OpenAI.setDist Λ (S₀.map (Function.Embedding.subtype _)) a.1 := by
  simp only [setDist, OpenAI.setDist, Finset.inf_map]
  refine Finset.inf_congr rfl fun y _ => ?_
  simp only [Function.comp_apply, Function.Embedding.coe_subtype]
  exact (domainEDist_of_mem a.2 y.2).symm

/-- On the induced square-lattice graph of `Λ`, the designated support is the repository's
`OpenAI.designatedSupport` of the same anchor and truncation set, read in `ℤ²`. -/
theorem map_designatedSupport_domainGraph (S₀ : Finset ↥(Λ : Set (ℤ × ℤ))) (r₀ : ℕ)
    (a : ↥(Λ : Set (ℤ × ℤ))) :
    (designatedSupport ((hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ))) S₀ r₀ a).map
        (Function.Embedding.subtype _) =
      OpenAI.designatedSupport Λ (S₀.map (Function.Embedding.subtype _)) r₀ a.1 := by
  ext z
  simp only [designatedSupport, OpenAI.designatedSupport, setDist_domainGraph]
  split_ifs with h
  · simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coe_subtype, domainComponent]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, by rw [domainEDist_of_mem a.2 y.2]; exact
        SimpleGraph.edist_ne_top_iff_reachable.mpr hy⟩
    · rintro ⟨hz, hne⟩
      refine ⟨⟨z, hz⟩, ?_, rfl⟩
      rw [domainEDist_of_mem a.2 hz] at hne
      exact SimpleGraph.edist_ne_top_iff_reachable.mp hne
  · simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coe_subtype, mem_graphNbhd_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, by rw [domainEDist_of_mem y.2 a.2, SimpleGraph.edist_comm]; exact hy⟩
    · rintro ⟨hz, hle⟩
      refine ⟨⟨z, hz⟩, ?_, rfl⟩
      rw [domainEDist_of_mem hz a.2, SimpleGraph.edist_comm] at hle
      exact hle

end DomainGraph

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

namespace CollarScan

variable (S : CollarScan V I)

/-- The actual compact set used for truncation: the chosen color through depth `L`. -/
def truncationSet (L : ℕ) : Finset V := S.A.filter fun x ↦ S.depth x ≤ L

/-- The actual old middle is contained in the original compact truncation set. -/
theorem middle_subset_truncationSet {k L : ℕ} (h : History S.K S.m S.M k)
    (g : Fin S.K) (hL : 8 * S.K * S.m ≤ L) :
    middle (S.oldChargeState h g) ⊆ S.truncationSet L := by
  intro x hx
  have hn := (Finset.mem_filter.mp hx).2
  have hA := (initial_middle_depth S.A S.depth _ _
    (S.oldChargeState_initial_none h g x hn) false).1
  exact Finset.mem_filter.mpr ⟨hA,
    (Finset.mem_Icc.mp (S.oldChargeState_depth_bounds h g hL x hn)).2⟩

omit [Fintype I] [LinearOrder I] in
/-- A designated support meeting a receiving side and the middle of a partition
whose middle lies in the truncation set is the actual base-radius ball, including
the variable-radius truncation case. Source: `08-scanner.tex`, lines 225–233. -/
theorem designatedSupport_eq_ball_of_incidence [Finite I] (σ : PhysicalPartition V) {L : ℕ}
    (side : Bool) (i : I) (hsub : middle σ ⊆ S.truncationSet L)
    (hsplit :
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i) ∩
        receiving σ side).Nonempty ∧
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i) ∩
        middle σ).Nonempty) :
    designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i) = S.ball i := by
  classical
  cases nonempty_fintype I
  have hcross : i ∈ crossingLabels S.graph (S.truncationSet L) S.r₀ S.anchor (middle σ) := by
    obtain ⟨x, hx⟩ := hsplit.2
    obtain ⟨y, hy⟩ := hsplit.1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ⟨x, (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩,
      y, (Finset.mem_inter.mp hy).1, ?_⟩
    have hs := (Finset.mem_filter.mp (Finset.mem_inter.mp hy).2).2
    simp [middle, hs]
  simpa only [ball] using (truncationRadius_eq_of_mem_crossingLabels hsub hcross).2.2

/-- Splitting designated supports, including the variable-radius truncation case,
are exactly the base-radius balls that the actual charge lottery selects. -/
theorem designatedSupport_eq_ball_of_split {k L : ℕ} (h : History S.K S.m S.M k)
    (g : Fin S.K) (side : Bool) (i : I) (hL : 8 * S.K * S.m ≤ L)
    (hsplit :
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i) ∩
        receiving (S.oldChargeState h g) side).Nonempty ∧
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i) ∩
        middle (S.oldChargeState h g)).Nonempty) :
    designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i) = S.ball i :=
  S.designatedSupport_eq_ball_of_incidence _ side i (S.middle_subset_truncationSet h g hL) hsplit

/-- Each splitting truncated designated support is sampled by the actual finite
history with probability `1/(2M) ≥ c/(nD)`, and the extended history removes its
exact old unassigned part. The probability is classical, before state transport. -/
theorem good_designated_split_sampling_domainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (↥(Λ : Set (ℤ × ℤ))) I)
    (hgraph : S.graph = (hasse ℤ □ hasse ℤ).induce (Λ : Set (ℤ × ℤ)))
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L μ : ℕ}
    (h : History S.K S.m S.M k) (g : Fin S.K) (side : Bool) (i : I)
    (hn : 2 ≤ S.n) (hm : 2 ≤ S.m) (hk : k + 1 ≤ S.n * S.m)
    (hr : 2 * S.r₀ ≤ S.D) (hD : 4 * S.D ≤ S.m) (hDpos : 1 ≤ S.D)
    (hL : 8 * S.K * S.m ≤ L) (hC : 3 * (μ : ℝ) ≤ S.C₁)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hmult : ∀ x, (Finset.univ.filter fun i ↦ S.anchor i = x).card ≤ μ)
    (hclear : ∀ t ∈ T, ∀ z ∈ cutEndpoints Λ (S.A.map (Function.Embedding.subtype _)),
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    (hgood : S.IsGoodOldHistory h)
    (hsplit :
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i) ∩
        receiving (S.oldChargeState h g) side).Nonempty ∧
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i) ∩
        middle (S.oldChargeState h g)).Nonempty) :
    ∃! slot : Fin S.M,
      S.selected g (h.1 g) (k + 1) (side, slot) = some i ∧
      (∀ c : ChargeChoices S.K S.M, c g = (side, slot) →
        middle (S.oldChargeState h g) \ middle (S.state (extendHistory h c) g) =
          designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i) ∩
            middle (S.oldChargeState h g)) ∧
      (∑ c : ChargeChoices S.K S.M, if c g = (side, slot) then chargeWeight c else 0) =
        1 / (2 * (S.M : ℝ)) ∧
      0 < 1 / (2 * (S.C₁ + 1)) ∧
      (1 / (2 * (S.C₁ + 1))) / ((S.n : ℝ) * S.D) ≤
        ∑ c : ChargeChoices S.K S.M, if c g = (side, slot) then chargeWeight c else 0 := by
  have heq := S.designatedSupport_eq_ball_of_split h g side i hL hsplit
  simpa only [heq] using good_split_sampling_domainGraph hT S hgraph hdepth h g side i
    hn hm hk hr hD hDpos hL hC hrows hmult hclear hgood (by simpa only [heq] using hsplit)

end CollarScan

end OpenAI.Scan
