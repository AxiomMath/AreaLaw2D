import AreaLawRefactored.S10_Amplification
import AreaLawRefactored.S11_Geometry

/-!
# §1 Theorem 1.1 and Corollary 1.2

Digest `digest/01-introduction.md`; the proof of Theorem 1.1 is D11.26
(`paper/sections/10-geometry.tex`, §11.8).

Propositions 9.6 and 10.2 enter through their frozen statements `OpenAI.CollarBound` and
`OpenAI.Amplification`, taken as hypotheses; Proposition 11.2 is `AreaLaw.Geometry.prop_11_2`,
Lemma 11.1 is `lemma_11_1` and Lemma 2.2 is `lemma_2_2`. In `theorem_1_1'` and `corollary_1_2'`
Proposition 10.2 is discharged by `amplification_complex`, which needs `1 ≤ q`; Proposition 9.6
remains a hypothesis.
-/

namespace AreaLaw

open Arealaw OpenAI Finset AreaLaw.Geometry
open scoped Matrix

/-! ## D1.4 Theorem 1.1 -/

/-- D1.4 **Theorem 1.1** (area law), proof D11.26. For all integers `q ≥ 1`, `R ≥ 0` and reals
`J > 0`, `Δ > 0` there is a finite `C = C(q,R,J,Δ)` such that: for every finite induced
square-lattice domain `Λ ⊂ ℤ²`, every admissible Hamiltonian `H` on `𝓗_Λ` with a unique
normalized ground vector `Ω`, ground energy `E₀` and `H - E₀ ≥ Δ(1 - |Ω⟩⟨Ω|)`, and every
`A ⊆ Λ`, `S_Ω(A) ≤ C |∂_Λ A|`. -/
theorem theorem_1_1 {q R : ℕ} {J Δ : ℝ} (hΔ : 0 < Δ) (prop_9_6 : CollarBound ℂ q R J Δ)
    (prop_10_2 : Amplification ℂ q R J Δ p) : AreaLaw ℂ q R J Δ := by
  -- D11.26.2: `n_*` from Propositions 9.6 and 10.2, then Proposition 11.2 at `n_*`
  obtain ⟨Ctpl, CM, hCM, nStar, hnStar, hinfo⟩ :=
    step_11_26_2 prop_9_6 prop_10_2 (2 * R + 11) (by linarith)
  obtain ⟨C₁, hdec⟩ := prop_11_2 (2 * R + 11) Ctpl nStar hnStar
  refine ⟨C₁ * (Real.log q + CM / 2), fun Λ Φ hΦ Ω hΩ E₀ hE hgap A hA => ?_⟩
  -- D11.26.1: `b = 0` by Lemma 2.2
  rcases Nat.eq_zero_or_pos (edgeBoundary Λ A).card with hb | hb
  · rw [hamiltonian_eq_graph] at hE hgap
    have h0 := lemma_2_2 squareLattice (isAdmissible_iff_graph.1 hΦ) hΩ hE hgap hΔ hA
      (edgeBoundary_eq_graph ▸ card_eq_zero.1 hb)
    rw [h0, hb]
    simp
  obtain ⟨D, m, X, f, T, n, s, hAD, hDX, hXX, hD, hi, hsum⟩ := hdec Λ A hA hb
  have hDA : D ⊆ A := hAD ▸ subset_union_left
  have hXΛ (i : Fin m) : X i ⊆ Λ := ((hi i).2.1.trans inter_subset_left).trans hA
  have hε (i : Fin m) : (pureState Ω hΩ).mutualInfo (hXΛ i)
      (union_subset sdiff_subset (biUnion_subset.2 fun j _ => hXΛ j) :
        Λ \ A ∪ (univ.filter fun j => f j = f i ∧ j < i).biUnion X ⊆ Λ) ≤
      CM * ((n i : ℝ) ^ 100)⁻¹ := by
    obtain ⟨-, hXi, hni, htpl, hsep, hL, hcut, hprev⟩ := hi i
    obtain ⟨r, hr, hI⟩ := hinfo Λ Φ hΦ Ω hΩ E₀ hE hgap A hA (T i) (n i) (s i) htpl hsep hL hni
    -- D11.26.3: `J_i ⊆ Λ \ N^Λ_{2r_i}(S_i)`, the whole `J_i` at once
    have hfilt : (univ.filter fun j => j < i ∧ f j = f i) =
        univ.filter fun j => f j = f i ∧ j < i := filter_congr fun _ _ => and_comm
    rw [hfilt] at hprev
    have hJ := step_11_26_3_two (n := n i) (biUnion_subset.2 fun j _ => hXΛ j) hr hcut hprev
    -- D11.26.4: Proposition 10.2 for `X_i ⊆ A ∩ T_i`
    exact hI (X i) hXi _ hJ
  -- D11.26.5: Lemma 11.1 with `ε_i = C n_i^{-100}` and `S(D) ≤ |D| log q`
  have hcancel := lemma_11_1 Λ Ω hΩ A D hA (hDA.trans hA) m X hXΛ f _ hAD hDX hXX hε
  have hDent : (pureState Ω hΩ).regionEntropy (hDA.trans hA) ≤ D.card * Real.log q := by
    have h := ((pureState Ω hΩ).restrict (hDA.trans hA)).entropy_le_log_card
    rwa [card_reg_const (fun _ => Fintype.card_fin q), Nat.cast_pow, Real.log_pow] at h
  have hlog : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hD' := mul_le_mul_of_nonneg_right hD hlog
  have hsum' := mul_le_mul_of_nonneg_left hsum hCM
  rw [← mul_sum] at hcancel
  -- D11.26.6: `C' = C₁ (log q + C/2)` depends on `q, R, J, Δ` only
  nlinarith

/-- D1.4 **Theorem 1.1** with Proposition 10.2 discharged by `amplification_complex` at
`p = 10⁶`; the remaining hypothesis is Proposition 9.6. -/
theorem theorem_1_1' {q R : ℕ} {J Δ : ℝ} (hq : 1 ≤ q) (hΔ : 0 < Δ)
    (prop_9_6 : CollarBound ℂ q R J Δ) : AreaLaw ℂ q R J Δ :=
  theorem_1_1 hΔ prop_9_6 (amplification_complex q R J Δ p hq hΔ le_rfl)

/-! ## D1.7 Corollary 1.2 -/

section D17

variable {σ : Type*} [DecidableEq σ] (G : SimpleGraph σ) [DecidableRel G.Adj] {k : ℕ}

/-- D1.7.3. In a graph of degree at most `k`, each `x ∈ ∂_in A` has at most `k` crossing edges:
`|∂_Λ A| ≤ k |∂_in A|`. -/
theorem step_1_7_3 (hdeg : ∀ (x : σ) (S : Finset σ), #(S.filter (G.Adj x)) ≤ k)
    (Λ A : Finset σ) :
    #(GraphDomain.edgeBoundary G Λ A) ≤ k * #((GraphDomain.edgeBoundary G Λ A).image Prod.fst) := by
  set E := GraphDomain.edgeBoundary G Λ A
  have hsub : E ⊆ (E.image Prod.fst).biUnion fun x => ((Λ \ A).filter (G.Adj x)).map
      (Function.Embedding.sectR x σ) := by
    intro e he
    obtain ⟨hx, hy, hxy⟩ := (SimpleGraph.mem_interedges_iff _).1 he
    exact mem_biUnion.2 ⟨e.1, mem_image_of_mem _ he, mem_map.2 ⟨e.2, mem_filter.2 ⟨hy, hxy⟩, rfl⟩⟩
  calc #E ≤ _ := card_le_card hsub
    _ ≤ ∑ x ∈ E.image Prod.fst, #(((Λ \ A).filter (G.Adj x)).map
        (Function.Embedding.sectR x σ)) := card_biUnion_le
    _ ≤ ∑ _x ∈ E.image Prod.fst, k := sum_le_sum fun x _ => (card_map _).le.trans (hdeg x _)
    _ = k * #(E.image Prod.fst) := by rw [sum_const, smul_eq_mul, mul_comm]

/-- D1.7.5. Each `v ∈ Z_A` carries between `1` and `k` crossing edges and every edge is counted
at both endpoints: `2 |∂_Λ A| ≤ k |Z_A|`. -/
theorem step_1_7_5 (hdeg : ∀ (x : σ) (S : Finset σ), #(S.filter (G.Adj x)) ≤ k)
    (Λ A : Finset σ) :
    2 * #(GraphDomain.edgeBoundary G Λ A) ≤ k * #(GraphDomain.cutEndpoints G Λ A) := by
  set E := GraphDomain.edgeBoundary G Λ A
  have hsnd : #E ≤ k * #(E.image Prod.snd) := by
    have hsub : E ⊆ (E.image Prod.snd).biUnion fun y => (A.filter (G.Adj y)).map
        (Function.Embedding.sectL σ y) := by
      intro e he
      obtain ⟨hx, hy, hxy⟩ := (SimpleGraph.mem_interedges_iff _).1 he
      exact mem_biUnion.2 ⟨e.2, mem_image_of_mem _ he,
        mem_map.2 ⟨e.1, mem_filter.2 ⟨hx, hxy.symm⟩, rfl⟩⟩
    calc #E ≤ _ := card_le_card hsub
      _ ≤ ∑ y ∈ E.image Prod.snd, #((A.filter (G.Adj y)).map
          (Function.Embedding.sectL σ y)) := card_biUnion_le
      _ ≤ ∑ _y ∈ E.image Prod.snd, k := sum_le_sum fun y _ => (card_map _).le.trans (hdeg y _)
      _ = k * #(E.image Prod.snd) := by rw [sum_const, smul_eq_mul, mul_comm]
  have hdisj : Disjoint (E.image Prod.fst) (E.image Prod.snd) := by
    rw [disjoint_left]
    rintro _ ha hb
    obtain ⟨e, he, rfl⟩ := mem_image.1 ha
    obtain ⟨e', he', h⟩ := mem_image.1 hb
    exact (mem_sdiff.1 ((SimpleGraph.mem_interedges_iff _).1 he').2.1).2
      (h ▸ ((SimpleGraph.mem_interedges_iff _).1 he).1)
  have hZ : #(GraphDomain.cutEndpoints G Λ A) = #(E.image Prod.fst) + #(E.image Prod.snd) :=
    card_union_of_disjoint hdisj
  have hfst := step_1_7_3 G hdeg Λ A
  rw [hZ]
  linarith

/-- A site of `ℤ²` has at most four neighbours in the square lattice. -/
theorem card_filter_squareLattice_adj_le (x : ℤ × ℤ) (S : Finset (ℤ × ℤ)) :
    #(S.filter (squareLattice.Adj x)) ≤ 4 := by
  refine (card_le_card fun y hy => ?_).trans (card_le_four (a := (x.1 + 1, x.2))
    (b := (x.1 - 1, x.2)) (c := (x.1, x.2 + 1)) (d := (x.1, x.2 - 1)))
  have h := (mem_filter.1 hy).2
  simp only [squareLattice, SimpleGraph.boxProd_adj, SimpleGraph.hasse_adj,
    Order.covBy_iff_add_one_eq] at h
  simp only [mem_insert, mem_singleton, Prod.ext_iff]
  omega

end D17

/-- D1.7 **Corollary 1.2.** (a) The conclusion of Theorem 1.1 holds for every subset of a finite
rectangular square lattice with bounded on-site and nearest-neighbour interactions and a unique
ground state separated by a fixed global gap. (b) For every domain covered by Theorem 1.1 and
with `C` its constant: `S_Ω(A) ≤ 4C |∂_in A|` and `S_Ω(A) ≤ 2C |Z_A|`. -/
theorem corollary_1_2 {q : ℕ} {J Δ : ℝ} (hΔ : 0 < Δ)
    (prop_9_6 : ∀ R, CollarBound ℂ q R J Δ) (prop_10_2 : ∀ R, Amplification ℂ q R J Δ p) :
    AreaLawCorollary ℂ q J Δ := by
  -- D1.7.1: rectangles are finite domains, on-site and nearest-neighbour terms have range `1`
  refine ⟨theorem_1_1 hΔ (prop_9_6 1) (prop_10_2 1), fun R => ?_⟩
  obtain ⟨C, hC⟩ := theorem_1_1 hΔ (prop_9_6 R) (prop_10_2 R)
  refine ⟨max C 0, fun Λ Φ hΦ Ω hΩ E₀ hE hgap A hA => ?_⟩
  have h := (hC Λ Φ hΦ Ω hΩ E₀ hE hgap A hA).trans
    (mul_le_mul_of_nonneg_right (le_max_left C 0) (Nat.cast_nonneg _))
  have h0 : 0 ≤ max C 0 := le_max_right C 0
  -- D1.7.3
  have h3 : ((edgeBoundary Λ A).card : ℝ) ≤ 4 * (innerBoundary Λ A).card := by
    exact_mod_cast step_1_7_3 squareLattice card_filter_squareLattice_adj_le Λ A
  -- D1.7.5
  have h5 : (2 * (edgeBoundary Λ A).card : ℝ) ≤ 4 * (cutEndpoints Λ A).card := by
    exact_mod_cast step_1_7_5 squareLattice card_filter_squareLattice_adj_le Λ A
  -- D1.7.6: with empty boundary the inequalities read `0 ≤ 0`
  refine ⟨h, h.trans ?_, h.trans ?_⟩
  · nlinarith
  · nlinarith

/-- D1.7 **Corollary 1.2** with Proposition 10.2 discharged by `amplification_complex`; the
remaining hypothesis is Proposition 9.6 for every range `R`. -/
theorem corollary_1_2' {q : ℕ} {J Δ : ℝ} (hq : 1 ≤ q) (hΔ : 0 < Δ)
    (prop_9_6 : ∀ R, CollarBound ℂ q R J Δ) : AreaLawCorollary ℂ q J Δ :=
  corollary_1_2 hΔ prop_9_6 fun R => amplification_complex q R J Δ p hq hΔ le_rfl

end AreaLaw
