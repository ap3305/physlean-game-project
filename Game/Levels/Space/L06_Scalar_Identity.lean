import Game.Metadata
import Game.Theorems.Space.Theorems
import Game.Theorems.Space.TheoremDocs

World "Space"
Level 6

Title ""

Introduction ""

Statement (u : Space) : (1 : ℝ) • u = u := by
  ext
  change 1 * u.x = u.x
  rw [one_mul]
  change 1 * u.y = u.y
  rw [one_mul]
  change 1 * u.z = u.z
  rw [one_mul]

Conclusion ""

NewTheorem vector_add_assoc one_mul mul_one
