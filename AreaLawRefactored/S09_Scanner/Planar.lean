import AreaLawRefactored.S09_Scanner.Interfaces

/-!
# §9 The planar depth and the `ℤ × ℤ` instance of Proposition 9.2

Digest `digest/09-scanner.md` D9.1, D9.3, D9.9. On `ℤ × ℤ` the depth is `dist_∞(·, T)` for a
finite nonempty target `T`, the graph is `squareLattice` with ball growth `v 2`, and the frozen
`OpenAI.IsAdmissible`, `OpenAI.hamiltonian` and `OpenAI.cutEndpoints` are the graph objects.
`prop_9_2_planar` is `Prop_9_2` in this form, for Propositions 9.5 and 9.6.
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix Filter Topology Arealaw Finset
open OpenAI (pureState HasGlobalGap ambientDilation ambientEDist)

namespace AreaLaw.Scanner

/-! ## D9.1 The depth -/

section Depth

variable (T : Finset (ℤ × ℤ)) (hT : T.Nonempty)

/-- D9.1. The depth `dist_∞(x, T)` of a site `x` below a finite nonempty target `T`. -/
def depth (x : ℤ × ℤ) : ℕ := T.inf' hT fun y => max (x.1 - y.1).natAbs (x.2 - y.2).natAbs

variable {T hT}

theorem depth_le_iff {x : ℤ × ℤ} {j : ℕ} :
    depth T hT x ≤ j ↔ ∃ y ∈ T, (x.1 - y.1).natAbs ≤ j ∧ (x.2 - y.2).natAbs ≤ j := by
  simp [depth, Finset.inf'_le_iff]

/-- D9.1. `T_j = {x : dist_∞(x, T) ≤ j}`. -/
theorem mem_ambientDilation {x : ℤ × ℤ} {j : ℕ} :
    x ∈ ambientDilation T j ↔ depth T hT x ≤ j := by
  rw [depth_le_iff, OpenAI.ambientDilation, Finset.mem_add]
  constructor
  · rintro ⟨y, hy, b, hb, rfl⟩
    simp only [Finset.mem_Icc, Prod.le_def] at hb
    exact ⟨y, hy, by simp; omega, by simp; omega⟩
  · rintro ⟨y, hy, h₁, h₂⟩
    refine ⟨y, hy, x - y, ?_, add_sub_cancel y x⟩
    simp only [Finset.mem_Icc, Prod.le_def, Prod.fst_sub, Prod.snd_sub]
    omega

/-- D9.1. The sites of depth `0` are the target. -/
theorem depth_eq_zero {x : ℤ × ℤ} : depth T hT x = 0 ↔ x ∈ T := by
  rw [← Nat.le_zero, depth_le_iff]
  refine ⟨fun ⟨y, hy, h₁, h₂⟩ => ?_, fun hx => ⟨x, hx, by simp, by simp⟩⟩
  rwa [Prod.ext (by omega : x.1 = y.1) (by omega : x.2 = y.2)]

/-- D9.1. The depth changes by at most one along an edge of `ℤ²`. -/
theorem depth_le_depth_add_one {x y : ℤ × ℤ} (h : squareLattice.Adj x y) :
    depth T hT x ≤ depth T hT y + 1 := by
  obtain ⟨z, hz, hzy⟩ := T.exists_mem_eq_inf' hT
    fun z => max (y.1 - z.1).natAbs (y.2 - z.2).natAbs
  simp only [squareLattice, SimpleGraph.boxProd_adj, SimpleGraph.hasse_adj,
    Order.covBy_iff_add_one_eq] at h
  rw [depth, depth, hzy]
  exact (Finset.inf'_le _ hz).trans (by omega)

/-- D9.3. The clearance `dist_∞(T, Z) > N` bounds the depth of every point of `Z`. -/
theorem lt_depth_of_lt_ambientEDist {Z : Finset (ℤ × ℤ)} {N : ℕ}
    (h : (N : ENNReal) < ambientEDist T Z) {z : ℤ × ℤ} (hz : z ∈ Z) : N < depth T hT z := by
  obtain ⟨y, hy, hyz⟩ := T.exists_mem_eq_inf' hT
    fun y => max (z.1 - y.1).natAbs (z.2 - y.2).natAbs
  have hint : ∀ a b : ℤ, edist a b = ((b - a).natAbs : ENNReal) := fun a b => by
    rw [edist_dist, Int.dist_eq, ← ENNReal.ofReal_natCast, Nat.cast_natAbs, Int.cast_abs,
      Int.cast_sub, abs_sub_comm]
  have hle : ambientEDist T Z ≤ edist y z :=
    (iInf₂_le y hy).trans (Metric.infEDist_le_edist_of_mem hz)
  rw [Prod.edist_eq, hint, hint, ← Nat.mono_cast.map_max] at hle
  rw [depth, hyz]
  exact_mod_cast h.trans_le hle

theorem filter_depth_eq_zero (A : Finset (ℤ × ℤ)) :
    A.filter (fun x => depth T hT x = 0) = A ∩ T := by
  ext x
  simp [depth_eq_zero]

theorem filter_depth_pos_le (A : Finset (ℤ × ℤ)) (j : ℕ) :
    A.filter (fun x => 0 < depth T hT x ∧ depth T hT x ≤ j) = A ∩ (ambientDilation T j \ T) := by
  ext x
  simp [mem_ambientDilation (hT := hT), ← depth_eq_zero (hT := hT), Nat.pos_iff_ne_zero,
    and_comm]

theorem filter_depth_le (A : Finset (ℤ × ℤ)) (j : ℕ) :
    A.filter (fun x => depth T hT x ≤ j) = A ∩ ambientDilation T j := by
  ext x
  simp [mem_ambientDilation (hT := hT)]

end Depth

theorem up_subtype {σ : Type*} [DecidableEq σ] {Λ S : Finset σ} (h : S ⊆ Λ) :
    up (S.subtype (· ∈ Λ)) = S := by
  rw [up, Finset.subtype_map, Finset.filter_true_of_mem h]

/-! ## Proposition 9.2 on `ℤ × ℤ` -/

open Comparators in
/-- D9.9 **Proposition 9.2** on `ℤ × ℤ`: `Prop_9_2` with `G = squareLattice`, `V = v 2`,
`dep = dist_∞(·, T)`, the frozen Hamiltonian and admissibility, and the test geometry
`|T| ≤ C_T n²`, `|T_j \ T_{j-1}| ≤ n` (`1 ≤ j ≤ L`), `dist_∞(T, Z) > 2L + 10 r₀`;
`X = A ∩ T`, and the far region of D9.28.2 is `Λ \ S₀`, `S₀ = A ∩ T_L`. -/
theorem prop_9_2_planar (h92 : Prop_9_2.{0}) (q : ℕ) [NeZero q] (R : ℕ) (J Δ : ℝ) (hΔ : 0 < Δ)
    (ℓ κ μ ν e Ce CT : ℝ) (hℓ : 0 < ℓ) (hℓ₁ : ℓ < 1) (hκ : 0 < κ) (hκμ : κ < μ)
    (hμ : μ < 1 - ℓ) (hν : 0 < ν) (he : 0 < e) (he₁ : e < 1) (hκe : κ ≤ e) (hCe : 0 < Ce)
    (hCT : 0 < CT) :
    ∃ (C₁ c Crl csh Csu Csl C₀ c₀ C Cl : ℝ) (n₀ : ℕ), 0 < C₁ ∧ 0 < c ∧ 0 < csh ∧
      0 < Csl ∧ 0 < Csu ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ W : ℝ, 1 ≤ W → a ℓ μ W n * (r₀ C₁ n : ℝ) ^ 2 ≤ c →
      ∀ (Λ : Finset (ℤ × ℤ))
        (Φ : (X : Finset (ℤ × ℤ)) → Matrix (Reg (OpenAI.Qudits q) X) (Reg (OpenAI.Qudits q) X) ℂ),
        OpenAI.IsAdmissible Λ R J Φ →
      ∀ (Ω : Reg (OpenAI.Qudits q) Λ → ℂ) (hΩ : star Ω ⬝ᵥ Ω = 1) (E₀ : ℝ),
        OpenAI.hamiltonian Λ Φ *ᵥ Ω = (E₀ : ℂ) • Ω →
        HasGlobalGap (OpenAI.hamiltonian Λ Φ) Ω E₀ Δ →
      ∀ (A : Finset (ℤ × ℤ)) (hA : A ⊆ Λ) (T : Finset (ℤ × ℤ)), T.Nonempty →
        (#T : ℝ) ≤ CT * (n : ℝ) ^ 2 →
        (∀ j, 1 ≤ j → j ≤ L ℓ n → #(ambientDilation T j \ ambientDilation T (j - 1)) ≤ n) →
        ((2 * L ℓ n + 10 * r₀ C₁ n : ℕ) : ENNReal) < ambientEDist T (OpenAI.cutEndpoints Λ A) →
        (pureState Ω hΩ).regionEntropy (inter_subset_left.trans hA : A ∩ T ⊆ Λ) ≤
          Ce * (n : ℝ) ^ (1 + e) →
        (∀ j ≤ L ℓ n, (pureState Ω hΩ).regionEntropy
            (inter_subset_left.trans hA : A ∩ (ambientDilation T j \ T) ⊆ Λ) ≤
          Ce * ((n : ℝ) * (L ℓ n : ℝ) ^ e + n)) →
      ∃ (X Fr : Finset Λ), up X = A ∩ T ∧ up Fr = Λ \ (A ∩ ambientDilation T (L ℓ n)) ∧
      ∃ (Dt : PhysData (fun _ : Λ => q)) (E : TypicalSet Dt X)
        (St : Type) (_ : Fintype St) (_ : DecidableEq St) (Γ : Statuses Λ (K ℓ μ n) St X)
        (l : ∀ k : ℕ, IrrepLabel (Equiv.Perm (Fin k))) (𝓡 : Finset (Finset Λ))
        (Bsh Bexc 𝓑 : ℝ),
        -- D9.9.1: transfer `Ω → Ω̃`
        (∀ Q : Finset Λ,
          |Dt.S Q - (pureState Ω hΩ).regionEntropy (up_subset Q)| ≤
            (n : ℝ) ^ (-200 : ℝ) * (1 + #Q)) ∧
        (∀ Q Q' : Finset Λ, Disjoint Q Q' →
          |Dt.I Q Q' - (pureState Ω hΩ).mutualInfo (up_subset Q) (up_subset Q')| ≤
            (n : ℝ) ^ (-200 : ℝ) * (1 + #Q)) ∧
        -- D9.9.2: comparator data
        E.w = (n : ℝ) ^ (3 / 5 : ℝ) ∧ 1 - (n : ℝ) ^ (-100 : ℝ) ≤ E.z ∧
        PrefixData Dt Γ 𝓡 Bsh Bexc ∧ Bsh ≤ C * ((n : ℝ) * (L ℓ n : ℝ) ^ e + n) ∧
        Bexc ≤ C * n * D κ n ∧
        MgfData Dt Γ C₀ c₀ 𝓑 ∧ 𝓑 ≤ C * n * D κ n * Real.log n ^ Cl ∧
        -- D9.28.2: the far region `Λ \ S₀` lies in every `V`
        (∀ s g, Fr ⊆ Γ.V s g) ∧
        -- the norm comparisons of Proposition 8.1
        RoughUpper Dt Γ E (a ℓ μ W n) l Bsh Bexc ∧
        (∀ τ : ℝ, 0 < τ → τ < 1 / 2 → RoughLower Dt Γ E Crl (a ℓ μ W n) τ l) ∧
        (a ℓ μ W n ≤ csh / Real.sqrt 𝓑 → SharpUpper Dt Γ E Csu (a ℓ μ W n) 𝓑 l ∧
          ∀ τ : ℝ, 0 < τ → τ < 1 / 2 → SharpLower Dt Γ E Csl (a ℓ μ W n) τ 𝓑 l) ∧
        -- the selected point
        ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧ ∀ k : ℕ, 0 < k →
          ∃ T' : Transport.MeanTree St,
            Edef Dt Γ E T' (a ℓ μ W n) k (l k) ≤
              C * (n : ℝ) ^ ℓ * (D κ n : ℝ) ^ 2 * W ^ 2 * Real.log n ^ Cl *
                  ((C * (n : ℝ) ^ ν * ((n : ℝ) ^ (e - μ) +
                      a ℓ μ W n ^ (1 / 4 : ℝ) * Real.log n ^ Cl)) ^ (1 / 8 : ℝ) +
                    (n : ℝ) ^ (-ν) + (n : ℝ) ^ (-100 : ℝ)) +
                C * (n : ℝ) ^ (-1000 : ℝ) + r k := by
  have hV : ∀ r : ℕ, (v 2 r : ℝ) ≤ 2 * (r + 1) ^ 2 := fun r => by
    rw [v_two]; push_cast; nlinarith
  obtain ⟨C₁, c, Crl, csh, Csu, Csl, C₀, c₀, C, Cl, n₀, hC₁, hc, hcsh, hCsl, hCsu, H⟩ :=
    h92 squareLattice (v 2) eq_ball_count_two 2 2 zero_le_two hV q R J Δ hΔ ℓ κ μ ν e Ce CT
      hℓ hℓ₁ hκ hκμ hμ hν he he₁ hκe hCe hCT
  refine ⟨C₁, c, Crl, csh, Csu, Csl, C₀, c₀, C, Cl, n₀, hC₁, hc, hcsh, hCsl, hCsu,
    fun n hn W hW har Λ Φ hΦ Ω hΩ E₀ hE hgap A hA T hT hTcard hrow hclear hSX hSQ => ?_⟩
  -- D9.3: the test geometry of `dist_∞(·, T)`
  have hgeom : TestGeometry squareLattice Λ A (depth T hT) CT n (L ℓ n) (r₀ C₁ n) := by
    refine ⟨fun x y h => depth_le_depth_add_one h, ?_, fun j hj hjL => ?_, fun z hz => ?_⟩
    · refine le_trans ?_ hTcard
      exact_mod_cast card_le_card fun x hx => depth_eq_zero.1 (mem_filter.1 hx).2
    · refine (card_le_card fun x hx => ?_).trans (hrow j hj hjL)
      rw [Finset.mem_sdiff, mem_ambientDilation (hT := hT), mem_ambientDilation (hT := hT)]
      have := (mem_filter.1 hx).2
      omega
    · exact_mod_cast lt_depth_of_lt_ambientEDist hclear hz
  obtain ⟨Dt, E, St, i₁, i₂, Γ, l, 𝓡, Bsh, Bexc, 𝓑, H⟩ :=
    H n hn W hW har Λ Φ (AreaLaw.isAdmissible_iff_graph.1 hΦ) Ω hΩ E₀ hE hgap A hA
      (depth T hT) hgeom
      (by rwa [(pureState Ω hΩ).regionEntropy_congr (filter_depth_eq_zero A)])
      (fun j hj => by
        rw [(pureState Ω hΩ).regionEntropy_congr (filter_depth_pos_le A j)]
        exact hSQ j hj)
  refine ⟨_, _, ?_, ?_, Dt, E, St, i₁, i₂, Γ, l, 𝓡, Bsh, Bexc, 𝓑, H⟩
  · rw [up_subtype ((filter_subset _ A).trans hA), filter_depth_eq_zero A]
  · rw [up_subtype sdiff_subset, filter_depth_le A]

end AreaLaw.Scanner
