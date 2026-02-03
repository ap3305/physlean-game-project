import Game.Metadata
import Game.Theorems.Space.Theorems
import Game.Theorems.Space.TheoremDocs

World "Space"
Level 2

Title ""

Introduction ""

Statement (u : Space) : u + (-u) = 0 := by
  ext
  rw [add_x]
  change u.x + -u.x = 0
  rw [add_neg_cancel]
  rw [add_y]
  change u.y + -u.y = 0
  rw [add_neg_cancel]
  rw [add_z]
  change u.z + -u.z = 0
  rw [add_neg_cancel]

Conclusion ""

NewTheorem vector_add_zero add_neg_cancel neg_add_cancel
