import Game.Metadata
import Game.Theorems.Space.Theorems
import Game.Theorems.Space.TheoremDocs

World "Space"
Level 4

Title ""

Introduction ""

open MySpace

Statement (u v w : MySpace) : u + (v + w) = (u + v) + w := by
  ext
  all_goals
    simp
    rw [add_assoc]

Conclusion ""

NewTheorem MySpace.vector_add_comm
