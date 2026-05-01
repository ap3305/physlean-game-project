import Game.Metadata
import Game.Theorems.Space.Theorems
import Game.Theorems.Space.TheoremDocs

World "Space"
Level 7

Title "vector_add_smul"

Introduction ""

open MySpace

Statement (v : MySpace) (a b : ℝ) : (a + b) • v = a • v + b • v := by
  ext
  Hint (hidden := true) "Your goal needs to be of the form $(a + b) * v.x = a * v.x + b * v.x$"
  change (a + b) * v.x = a * v.x + b * v.x
  ring
  change (a + b) * v.y = a * v.y + b * v.y
  ring
  change (a + b) * v.z = a * v.z + b * v.z
  ring

Conclusion ""

NewTactic ring
NewTheorem MySpace.vector_smul_add

DisabledTactic simp
DisabledTheorem add_mul mul_add
