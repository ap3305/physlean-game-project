import Game.Metadata
import Game.Theorems.Space.Theorems
import Game.Theorems.Space.TheoremDocs

World "Space"
Level 8

Title "vector_smul_assoc"

Introduction ""

open MySpace

Statement (v : MySpace) (a b : ℝ) : a • (b • v) = (a * b) • v := by
  ext
  all_goals
    simp
    ring

Conclusion ""

NewTheorem MySpace.vector_add_smul
