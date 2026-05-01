import Game.Metadata
import Game.Theorems.Space.Theorems
import Game.Theorems.Space.TheoremDocs

World "Space"
Level 6

Title ""

Introduction ""

open MySpace

Statement (u v : MySpace) (a : ℝ) : a • (u + v) = a • u + a • v := by
  ext
  Hint (hidden := true) "Your goal needs to be of the form $a * (u.x + v.x) = a * u.x + a * v.x$"
  change a * (u.x + v.x) = a * u.x + a * v.x
  rw [mul_add]
  change a * (u.y + v.y) = a * u.y + a * v.y
  rw [mul_add]
  change a * (u.z + v.z) = a * u.z + a * v.z
  rw [mul_add]

Conclusion ""

NewTheorem MySpace.vector_smul_one

DisabledTactic simp
