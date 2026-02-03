import Game.Metadata
import Game.Theorems.Space.Theorems
import Game.Theorems.Space.TheoremDocs

World "Space"
Level 8

Title ""

Introduction ""

Statement (u : Space) (a b : ℝ) : a • (b • u) = (a * b) • u := by
  ext
  change a * (b * u.x) = (a * b) * u.x
  rw [mul_assoc]
  change a * (b * u.y) = (a * b) * u.y
  rw [mul_assoc]
  change a * (b * u.z) = (a * b) * u.z
  rw [mul_assoc]

Conclusion ""

NewTheorem mul_assoc vector_add_smul
