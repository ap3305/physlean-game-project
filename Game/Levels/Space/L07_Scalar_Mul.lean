import Game.Metadata
import Game.Theorems.Space.Theorems
import Game.Theorems.Space.TheoremDocs

World "Space"
Level 7

Title ""

Introduction ""

Statement (u v : Space) (a : ℝ) : a * (u + v) = a * u + a * v := by
  ext
  change a * (u.x + v.x) = a * u.x + a * v.x
  rw [mul_add]

Conclusion ""

NewTheorem vector_mul_comm mul_add mul_add
