import Game.Metadata
import Game.Theorems.Space.Theorems
import Game.Theorems.Space.TheoremDocs

World "Space"
Level 3

Title "Back and Forth"

Introduction ""

Statement (u v : MySpace) : u + v = v + u := by
  ext
  change u.x + v.x = v.x + u.x
  rw [add_comm]
  change u.y + v.y = v.y + u.y
  rw [add_comm]
  change u.z + v.z = v.z + u.z
  rw [add_comm]

Conclusion ""

NewTheorem vector_add_inv
