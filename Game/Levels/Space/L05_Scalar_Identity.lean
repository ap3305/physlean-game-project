import Game.Metadata
import Game.Theorems.Space.Theorems
import Game.Theorems.Space.TheoremDocs

World "Space"
Level 5

Title "vector_smul_one"

Introduction "Now we're adding scalar multiplication into the mix, see if you can solve this one without using `simp`."

open MySpace

Statement (v : MySpace) : (1 : ℝ) • v = v := by
  Hint (hidden := true) "It might be useful to check back on earlier levels if you've forgotten how to use change."
  ext
  change 1 * v.x = v.x
  rw [one_mul]
  change 1 * v.y = v.y
  rw [one_mul]
  change 1 * v.z = v.z
  rw [one_mul]

Conclusion ""

NewTheorem MySpace.vector_add_assoc

DisabledTactic simp
