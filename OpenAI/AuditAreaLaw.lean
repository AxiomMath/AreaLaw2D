import OpenAI.AreaLaw

/-!
# Axiom audit of Theorem 1.1

`#print axioms` for Theorem 1.1 (`OpenAI.area_law`), Corollary 1.2 and the steps of the proof
of Theorem 1.1, confirming that each depends only on `propext`, `Classical.choice` and
`Quot.sound`.  Kept apart from `OpenAI.Audit`, which is over the repository's file-length
limit.
-/

-- The clearance of the exterior and of the earlier same-family regions.
#print axioms OpenAI.natCast_lt_ambientSupDistance_of_lt_ambientEDist
#print axioms OpenAI.graphNeighborhood_subset_of_lt_ambientEDist
#print axioms OpenAI.exterior_union_subset_graphNeighborhood_compl_of_lt_ambientEDist

-- The mutual-information bound from Propositions 9.6 and 10.2.
#print axioms OpenAI.exists_mutualInfo_exterior_union_le

-- Theorem 1.1 and Corollary 1.2.
#print axioms OpenAI.area_law
#print axioms OpenAI.area_law_corollary
