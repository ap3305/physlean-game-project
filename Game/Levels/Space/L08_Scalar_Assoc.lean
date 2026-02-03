import Game.Metadata
import Game.Theorems.Space.Theorems
import Game.Theorems.Space.TheoremDocs

World "Space"
Level 8

Title ""

Introduction ""

Statement (v : MySpace) (a b : ℝ) : a • (b • v) = (a * b) • v := by
  ext
  all_goals
    simp
    ring

Conclusion ""

NewTheorem vector_add_smul
