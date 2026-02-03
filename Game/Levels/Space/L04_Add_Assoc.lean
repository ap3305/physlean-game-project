import Game.Metadata
import Game.Theorems.Space.Theorems
import Game.Theorems.Space.TheoremDocs

World "Space"
Level 4

Title ""

Introduction ""

Statement (u v w : Space) : u + (v + w) = (u + v) + w := by
  ext
  change u.x + (v.x + w.x) = (u.x + v.x) + w.x
  rw [add_assoc]
  change u.y + (v.y + w.y) = (u.y + v.y) + w.y
  rw [add_assoc]
  change u.z + (v.z + w.z) = (u.z + v.z) + w.z
  rw [add_assoc]

Conclusion ""

NewTheorem add_assoc vector_add_comm
