import AreaLaw.S06_Replicas.Labels
import AreaLaw.S06_Replicas.Surprisal
import AreaLawForMathlib.RepresentationTheory.SchurWeyl.SubsystemTransport
import AreaLawForMathlib.RepresentationTheory.SchurWeyl.WeylDimension
import AreaLawForMathlib.RepresentationTheory.SchurWeyl.MergeMoment
import AreaLawForMathlib.RepresentationTheory.SchurWeyl.GroupedCopies

/-!
# §6 Schur–Weyl labels (D6.2) and Lemma 6.1 (D6.4)

Paper `paper/sections/05-replicas.tex` lines 47–275. The partition of a label `l` is
`labelPart l` (rows from `0`), padded to length `q` it is `part q l`, with shifted parts
`Partition.shiftedPart (part q l)`.
-/

namespace AreaLaw.Replicas

open Matrix PermutationRepresentation TensorPower Finset
open scoped ComplexOrder

variable {I : Type*} [DecidableEq I] (ι : I → Type*) (k : ℕ)

/-! ## D6.2 Schur–Weyl decomposition -/

/-- D6.2 (`replicas:schur-decomposition`). The labels of `S_k` are the partitions `λ ⊢ k`
(non-increasing, sum `k`, padded with zeros), and on `(ℂ^q)^{⊗k}` the `[λ] ⊗ V_λ^{(q)}` block
of a label is nonzero exactly when `ℓ(λ) ≤ q`; the blocks resolve the identity and the block of
`λ` has dimension `d_λ · dim V_λ^{(q)}`. -/
theorem eq_replicas_schur_decomposition (q : ℕ) :
    Function.Bijective (fun l : IrrepLabel (Equiv.Perm (Fin k)) =>
      (⟨labelShape l, labelShape_mem_padded l⟩ : Partition.padded k k)) ∧
    (∀ l : IrrepLabel (Equiv.Perm (Fin k)),
      labelProj (TensorPower.copyPerm (Fin q) k) l ≠ 0 ↔ ∀ a, q ≤ a → labelPart l a = 0) ∧
    ∑ l, labelProj (TensorPower.copyPerm (Fin q) k) l = 1 ∧
    ∀ l : IrrepLabel (Equiv.Perm (Fin k)), (labelProj (TensorPower.copyPerm (Fin q) k) l).trace =
      (l.dim * PermutationRepresentation.multiplicity (TensorPower.copyPerm (Fin q) k) l : ℕ) := by
  refine ⟨labelShape_bijective, fun l => ?_, sum_labelProj _, trace_labelProj _⟩
  rw [labelProj_ne_zero_iff]
  refine ⟨fun h a ha => ?_, fun h i hi => by simpa [labelPart, i.2] using h i hi⟩
  simp only [labelPart]
  split_ifs with hak
  exacts [h ⟨a, hak⟩ ha, rfl]

/-! ## D6.4 Lemma 6.1 -/

/-- D6.4 (1). For `λ ⊢ k` with `ℓ(λ) ≤ q` and `l_i = λ_i + q - i`:
`dim V_λ^{(q)} = ∏_{i<j} (l_i - l_j)/(j - i)`, `d_λ = k! ∏_{i<j} (l_i - l_j)/∏_i l_i!` and
`log d_λ = k H(λ/k) + O_q(log(k + 2))`. The number of labels and `∑_λ dim V_λ^{(q)}` are at most
`poly(k)` (`q` fixed). -/
theorem lemma_6_1_1 (q : ℕ) :
    (∀ l : IrrepLabel (Equiv.Perm (Fin k)), (∀ a, q ≤ a → labelPart l a = 0) →
      (PermutationRepresentation.multiplicity (TensorPower.copyPerm (Fin q) k) l : ℝ) =
        Partition.weylFormula (part q l) ∧
      (l.dim : ℝ) = Partition.hookFormula (part q l) ∧
      |Real.log l.dim - Partition.entropyTerm (part q l)| ≤
        (q ^ 2 + q + 1) * (Real.log (k + q + 2) + 1)) ∧
    (univ.filter fun l : IrrepLabel (Equiv.Perm (Fin k)) =>
      labelProj (TensorPower.copyPerm (Fin q) k) l ≠ 0).card ≤ (k + 1) ^ (q ^ 2) ∧
    ∑ l : IrrepLabel (Equiv.Perm (Fin k)),
        PermutationRepresentation.multiplicity (TensorPower.copyPerm (Fin q) k) l ≤
      (k + 1) ^ (q ^ 2) := by
  refine ⟨fun l hrows => ⟨multiplicity_eq_weylFormula l hrows,
    dim_eq_hookFormula_of_rows l hrows, ?_⟩, by simpa using card_labelProj_ne_zero_le (Fin q) k,
    by simpa using sum_multiplicity_le (Fin q) k⟩
  -- D6.4.5
  have h := Partition.abs_log_hookFormula_sub_le (p := part q l)
    fun a b hab => labelPart_antitone l hab
  rwa [sum_labelPart_of_rows l hrows, ← dim_eq_hookFormula_of_rows l hrows] at h

variable [Fintype I] [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]

/-- D6.4 (3). `Q, E` disjoint, labels `λ, μ` compatible with the label `ν` on `QE`:
`d_ν ≤ d_λ d_μ` and `d_λ ≤ d_ν d_μ`. For a state on `(QE)^{⊗k}` (here `E = Q^c` in an arbitrary
system) invariant under the copy permutations of `Q` and of `E` — e.g. a tensor product of
permutation-invariant densities on `Q^{⊗k}`, `E^{⊗k}` — `Pr(ν | λ, μ) ≤ poly(k) d_ν/(d_λ d_μ)`,
hence `E (d_λ d_μ/d_ν)^b ≤ poly(k)` for `0 ≤ b ≤ 1`, uniformly in the state. -/
theorem lemma_6_1_3 :
    (∀ Q E : Finset I, Disjoint Q E → ∀ l μ ν : IrrepLabel (Equiv.Perm (Fin k)),
      π ι k Q l * π ι k E μ * π ι k (Q ∪ E) ν ≠ 0 →
        ν.dim ≤ l.dim * μ.dim ∧ l.dim ≤ ν.dim * μ.dim) ∧
    ∀ (Q : Finset I) (ρ : Matrix (Config ι k) (Config ι k) ℂ), ρ.PosSemidef →
      (∀ σ, Commute (U ι k Q σ) ρ) → (∀ σ, Commute (U ι k Qᶜ σ) ρ) →
      (∀ l μ ν : IrrepLabel (Equiv.Perm (Fin k)),
        (ρ * (π ι k Q l * π ι k Qᶜ μ * π ι k univ ν)).trace.re * (l.dim * μ.dim) ≤
          ((k + 1) ^ (Fintype.card ((f : I) → ι f) ^ 2) : ℕ) * ν.dim *
            (ρ * (π ι k Q l * π ι k Qᶜ μ)).trace.re) ∧
      (ρ.trace = 1 → ∀ b : ℝ, 0 ≤ b → b ≤ 1 →
        ∑ l, ∑ μ, ∑ ν, (ρ * (π ι k Q l * π ι k Qᶜ μ * π ι k univ ν)).trace.re *
          (((l.dim * μ.dim : ℕ) : ℝ) / ν.dim) ^ b ≤
            ((k + 1) ^ (Fintype.card ((f : I) → ι f) ^ 2) : ℕ)) := by
  have huniv : π ι k univ = labelProj (TensorPower.copyPerm ((f : I) → ι f) k) := by
    funext ν; rw [π, copyPerm, subsystemPerm_univ]
  refine ⟨fun Q E hQE l μ ν h => merge_dim_le hQE h, fun Q ρ hρ hQ hE => ⟨fun l μ ν => ?_,
    fun htr b _ hb => ?_⟩⟩
  · -- D6.4.11, D6.4.12
    rw [huniv]
    exact merge_conditional_le Q hρ hQ hE l μ ν
  · -- D6.4.13
    rw [huniv]
    exact merge_moment_le Q hρ htr hQ hE hb

/-- D6.4 (4). Copies split into groups of sizes `k - r` and `r` (by `e`); labels `α, β` of a fixed
subsystem `Q` on the two groups compatible with the full label `λ`:
`d_α d_β ≤ d_λ ≤ binom(k, r) d_α d_β`. The group label projectors commute with the full label
projector. -/
theorem lemma_6_1_4 {m r : ℕ} (e : Fin m ⊕ Fin r ≃ Fin k) (Q : Finset I)
    (α : IrrepLabel (Equiv.Perm (Fin m))) (β : IrrepLabel (Equiv.Perm (Fin r)))
    (l : IrrepLabel (Equiv.Perm (Fin k))) :
    (labelProj ((copyPerm ι k Q).comp (groupHom₁ e)) α *
        labelProj ((copyPerm ι k Q).comp (groupHom₂ e)) β * π ι k Q l ≠ 0 →
      α.dim * β.dim ≤ l.dim ∧ l.dim ≤ k.choose r * (α.dim * β.dim)) ∧
    Commute (labelProj ((copyPerm ι k Q).comp (groupHom₁ e)) α) (π ι k Q l) ∧
    Commute (labelProj ((copyPerm ι k Q).comp (groupHom₂ e)) β) (π ι k Q l) :=
  ⟨groupedCopies_dim e _, groupedCopies_commute e _ α β l⟩

/-- D6.4 (6). The star operator `J_{Q,k} = k⁻¹ ∑_{j<k} U_Q((j k))` on `k = m + 1` copies. -/
noncomputable def J (m : ℕ) (Q : Finset I) : Matrix (Config ι (m + 1)) (Config ι (m + 1)) ℂ :=
  starOp (copyPerm ι (m + 1) Q)

/-- D6.4 (6). On `k = m + 1` copies of `Q`, `q = d_Q`: the full label `λ` and the label `ν` of
the first `k - 1` copies are compatible iff `ν = λ - e_i` is a partition. In any
permutation-invariant `Q` state, conditional on `λ`,
`p_{λ,i} = d_{λ-e_i}/d_λ = (l_i/k) ∏_{a<b}(l_a - δ_{ai} - l_b + δ_{bi})/∏_{a<b}(l_a - l_b)
≤ 2^q l_i/k`. The star operator `J_{Q,k}` has eigenvalue `(λ_i - i)/k` on branch `i`
(`(labelPart l i - 1 - i)/k` with rows from `0`). -/
theorem lemma_6_1_6 (m : ℕ) (Q : Finset I) (l : IrrepLabel (Equiv.Perm (Fin (m + 1))))
    (n : IrrepLabel (Equiv.Perm (Fin m))) :
    (π ι (m + 1) Q l * labelProj ((copyPerm ι (m + 1) Q).comp (firstCopies m)) n ≠ 0 ↔
      π ι (m + 1) Q l ≠ 0 ∧
        ∃ i, labelPart l = Function.update (labelPart n) i (labelPart n i + 1)) ∧
    ∀ i, labelPart l = Function.update (labelPart n) i (labelPart n i + 1) →
      (π ι (m + 1) Q l ≠ 0 →
        ∀ ρ : Matrix (Config ι (m + 1)) (Config ι (m + 1)) ℂ,
          (∀ σ, Commute (U ι (m + 1) Q σ) ρ) →
        ∃ hi : i < Fintype.card (SubConfig ι Q),
          (l.dim : ℂ) * (ρ * (π ι (m + 1) Q l *
              labelProj ((copyPerm ι (m + 1) Q).comp (firstCopies m)) n)).trace =
            n.dim * (ρ * π ι (m + 1) Q l).trace ∧
          (n.dim : ℝ) / l.dim =
            (Partition.shiftedPart (part (Fintype.card (SubConfig ι Q)) l) ⟨i, hi⟩ /
                (m + 1 : ℕ)) *
              ∏ j ∈ univ.erase (⟨i, hi⟩ : Fin (Fintype.card (SubConfig ι Q))),
                ((Partition.shiftedPart (part (Fintype.card (SubConfig ι Q)) l) ⟨i, hi⟩ : ℝ) -
                    1 - Partition.shiftedPart (part (Fintype.card (SubConfig ι Q)) l) j) /
                  ((Partition.shiftedPart (part (Fintype.card (SubConfig ι Q)) l) ⟨i, hi⟩ : ℝ) -
                    Partition.shiftedPart (part (Fintype.card (SubConfig ι Q)) l) j) ∧
          (n.dim : ℝ) / l.dim ≤ 2 ^ Fintype.card (SubConfig ι Q) *
            (Partition.shiftedPart (part (Fintype.card (SubConfig ι Q)) l) ⟨i, hi⟩ /
              (m + 1 : ℕ))) ∧
      J ι m Q * (π ι (m + 1) Q l *
          labelProj ((copyPerm ι (m + 1) Q).comp (firstCopies m)) n) =
        (((labelPart l i : ℂ) - 1 - i) / (m + 1 : ℕ)) •
          (π ι (m + 1) Q l * labelProj ((copyPerm ι (m + 1) Q).comp (firstCopies m)) n) := by
  refine ⟨labelProj_mul_labelProj_firstCopies_ne_zero_iff _ l n, fun i h => ⟨fun hl ρ hρ => ?_,
    starOp_mul_branch _ h⟩⟩
  -- D6.4.17: `ℓ(λ) ≤ d_Q`
  have hrows := labelPart_eq_zero_of_subsystemPerm ι (m + 1) Q hl
  have hi : i < Fintype.card (SubConfig ι Q) := by
    by_contra hiq
    have hli : labelPart l i = labelPart n i + 1 := by rw [h, Function.update_self]
    rw [hrows i (not_lt.mp hiq)] at hli
    omega
  -- D6.4.18, D6.4.19
  exact ⟨hi, trace_mul_labelProj_mul_labelProj_firstCopies _ hρ ⟨i, h⟩,
    dim_div_dim_eq h hrows hi, dim_div_dim_le h hrows hi⟩

/-- D6.4, Lemma 6.1. The Schur-label estimates (1)–(6) for the systems of D6.1 (items (2), (5):
`lemma_6_1_2`, `lemma_6_1_5`); the polynomial bounds depend on the fixed subsystem dimensions
only. -/
theorem lemma_6_1 :
    (type_of% @lemma_6_1_1) ∧ (type_of% @lemma_6_1_2) ∧ (type_of% @lemma_6_1_3) ∧
      (type_of% @lemma_6_1_4) ∧ (type_of% @lemma_6_1_5) ∧ (type_of% @lemma_6_1_6) :=
  ⟨@lemma_6_1_1, @lemma_6_1_2, @lemma_6_1_3, @lemma_6_1_4, @lemma_6_1_5, @lemma_6_1_6⟩

end AreaLaw.Replicas
