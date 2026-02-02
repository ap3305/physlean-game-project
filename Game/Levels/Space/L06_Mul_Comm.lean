import Game.Metadata
import Game.Theorems.Space.Theorems
import Game.Theorems.Space.TheoremDocs

World "Space"
Level 6

Title ""

Introduction ""

Statement (u : Space) (a : ℝ) : a * u = u * a := by
  rfl

Conclusion ""

NewTheorem vector_add_comm
