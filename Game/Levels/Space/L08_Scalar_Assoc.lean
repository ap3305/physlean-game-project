import Game.Metadata
import Game.Theorems.Space.Theorems
import Game.Theorems.Space.TheoremDocs

World "Space"
Level 8

Title ""

Introduction ""

Statement (v : MySpace) (a b : ℝ) : a • (b • v) = (a * b) • v := by
  ext
  change a * (b * v.x) = (a * b) * v.x
  rw [mul_assoc]
  change a * (b * v.y) = (a * b) * v.y
  rw [mul_assoc]
  change a * (b * v.z) = (a * b) * v.z
  rw [mul_assoc]

Conclusion ""

NewTheorem mul_assoc vector_add_smul
