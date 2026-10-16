import OpenAI.Amplification

/-!
# Axiom audit of Proposition 10.2

`#print axioms` for Proposition 10.2 (`OpenAI.amplification`) and the load-bearing results of
its proof, confirming that each depends only on `propext`, `Classical.choice` and
`Quot.sound`.  Kept apart from `OpenAI.Audit`, which is over the repository's file-length
limit.
-/

-- Lemma 10.1: the truncation and omission estimates for products of positive constraints, and
-- the excited-state decay.
#print axioms OpenAI.exists_latticeConstraintWord_truncation
#print axioms OpenAI.exists_latticeConstraintWord_omission
#print axioms OpenAI.latticeConstraintWord_excitedProjection_decay
#print axioms OpenAI.norm_sub_spectatorCondExpect_le

-- The restoring operator, the ancilla unitary and the entropy comparison.
#print axioms OpenAI.exists_typicalProjectors_three_cuts
#print axioms OpenAI.restoringTransport_estimates
#print axioms OpenAI.exists_ancilla_unitary_of_good_realization
#print axioms OpenAI.mutualInformation_le_of_ancilla_unitary
#print axioms OpenAI.mutualInfo_pureState_eq_finiteProduct

-- The cut clearance and the reduction to the radius and output bounds.
#print axioms OpenAI.exists_threshold_graphNeighborhood_collar_subset
#print axioms OpenAI.amplification_of_amplificationOutput

-- The output over `ℂ`, its transfer to `RCLike 𝕜`, and Proposition 10.2.
#print axioms OpenAI.amplificationOutput_complex
#print axioms OpenAI.amplificationOutput
#print axioms OpenAI.amplification
