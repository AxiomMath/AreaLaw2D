import Solution.Basic

/-! # Axiom audit of the frozen statements

`lake env lean scripts/audit.lean` prints the axioms of the solution of the challenge and of
the declaration proving each frozen statement of `OpenAI/Statements.lean`. Each should depend
on `propext`, `Classical.choice` and `Quot.sound` only. -/

#print axioms OpenAI.Challenge.area_law
#print axioms AreaLaw.areaLaw
#print axioms AreaLaw.areaLawCorollary
#print axioms AreaLaw.positiveReplacement
#print axioms AreaLaw.collarBound_of_complex
#print axioms AreaLaw.Scanner.prop_9_6
#print axioms AreaLaw.amplification
#print axioms AreaLaw.twoFamilyCancellation
#print axioms AreaLaw.Geometry.prop_11_2
#print axioms AreaLaw.conditionalContinuity
#print axioms AreaLaw.marginalTails
#print axioms AreaLaw.bufferDiscount
#print axioms AreaLaw.initialBoxEstimate
