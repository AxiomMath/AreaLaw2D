import OpenAI.Cylinder3D

/-!
# Axiom audit of the three-dimensional theorems

`#print axioms` for the theorems proved about the statements of `OpenAI.Statements3D`,
confirming that each depends only on `propext`, `Classical.choice` and `Quot.sound`.
-/

-- Target B.1: cylinders over a planar domain.
#print axioms OpenAI.cylinderAreaLawOfPlanar3D
#print axioms OpenAI.cylinderAreaLaw3D
