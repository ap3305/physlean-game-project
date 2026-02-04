import Game.Metadata
import Game.Theorems.Space.Theorems
import Game.Theorems.Space.TheoremDocs

World "Space"
Level 3

Title "Back and Forth"

Introduction ""

Statement (u v : MySpace) : u + v = v + u := by
  ext
  all_goals
    simp
    rw[add_comm]

Conclusion ""

NewTactic simp all_goals
NewTheorem vector_add_inv
