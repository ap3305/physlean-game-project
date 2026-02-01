import Game.Metadata
import Game.Theorems.Space.Theorems
import Game.Theorems.Space.TheoremDocs

World "Space"
Level 2

Title ""

Introduction ""

Statement (u : Space) (h : u = ⟨1, 2, 3⟩) : u + (0 : Space) = u := by
  ext
  rw [add_x]
  change u.x + 0 = u.x
  rw [add_zero]
  rw [add_y]
  change u.y + 0 = u.y
  rw [add_zero]
  rw [add_z]
  change u.z + 0 = u.z
  rw [add_zero]

Conclusion ""

NewTactic ext
NewTheorem add_x add_y add_z add_zero
