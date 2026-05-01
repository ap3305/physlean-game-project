import Game.Metadata
import Game.Theorems.Space.Theorems
import Game.Theorems.Space.TheoremDocs

World "Space"
Level 3

Title "Back and Forth"

Introduction ""

open MySpace

Statement (u v : MySpace) : u + v = v + u := by
  ext
  simp
  rw [add_comm]
  Hint "Now try using the all_goals tactic to solve both remaining goals at once"
  all_goals
    simp
    rw [add_comm]

Conclusion ""

NewTactic simp all_goals
NewTheorem MySpace.vector_add_inv
