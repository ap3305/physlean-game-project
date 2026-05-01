import Game.Metadata
import Game.Theorems.Space.Theorems
import Game.Theorems.Space.TheoremDocs

World "Space"
Level 3

Title "vector_add_comm"

Introduction "To speed up this process, we can use `simp` to do automatically what we were using `change` to do by hand."

open MySpace

Statement (u v : MySpace) : u + v = v + u := by
  ext
  simp
  rw [add_comm]
  Hint "We can also use `all_goals` before another tactic to solve both remaining goals at once."
  Hint (hidden := true) "`all_goals` goes in the same like as the tactic it's applied to, for example `all_goals rw [h]`"
  all_goals
    simp
    rw [add_comm]

Conclusion ""

NewTactic simp all_goals
NewTheorem MySpace.vector_add_inv
