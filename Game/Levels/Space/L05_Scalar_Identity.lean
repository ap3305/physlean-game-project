import Game.Metadata
import Game.Theorems.Space.Theorems
import Game.Theorems.Space.TheoremDocs

World "Space"
Level 5

Title ""

Introduction ""

open MySpace

Statement (v : MySpace) : (1 : ℝ) • v = v := by
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
