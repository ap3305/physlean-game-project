import Game.Metadata
import Game.Theorems.Space.Theorems
import Game.Theorems.Space.TheoremDocs

World "Space"
Level 7

Title ""

Introduction ""

Statement (u : Space) (a b : ℝ) : (a + b) • u = a • u + b • u := by
  ext
  change (a + b) * u.x = a * u.x + b * u.x
  rw [add_mul]
  change (a + b) * u.y = a * u.y + b * u.y
  rw [add_mul]
  change (a + b) * u.z = a * u.z + b * u.z
  rw [add_mul]

Conclusion ""

NewTheorem vector_smul_add
