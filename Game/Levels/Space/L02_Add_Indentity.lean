import Game.Metadata
import Game.Theorems.Space.Theorems
import Game.Theorems.Space.TheoremDocs

World "Space"
Level 2

Title ""

Introduction ""

Statement (u : Space) : u + (0 : Space) = u := by
  ext
  change u.x + 0 = u.x
  rw [add_zero]
  change u.y + 0 = u.y
  rw [add_zero]
  change u.z + 0 = u.z
  rw [add_zero]

Conclusion ""

NewTactic ext
NewTheorem add_zero zero_add
DisabledTactic ring
