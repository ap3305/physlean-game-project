import Game.Metadata
import Game.Theorems.Space.Theorems
import Game.Theorems.Space.TheoremDocs

World "Space"
Level 2

Title ""

Introduction ""

Statement (v : MySpace) : v + (-v) = 0 := by
  ext
  rw [add_x]
  change v.x + -v.x = 0
  rw [add_neg_cancel]
  rw [add_y]
  change v.y + -v.y = 0
  rw [add_neg_cancel]
  rw [add_z]
  change v.z + -v.z = 0
  rw [add_neg_cancel]

Conclusion ""

NewTheorem vector_add_zero
