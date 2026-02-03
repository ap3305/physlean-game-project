import Game.Metadata
import Game.Theorems.Space.Theorems
import Game.Theorems.Space.TheoremDocs
import Mathlib.Tactic.Abel

World "Space"
Level 9

Title ""

Introduction ""

Statement (u v : MySpace) (a b c : ℝ) : (a * b) • (c • u + v) + (a * (b + c)) • v = a • ((b * c) • u + ((2 : ℝ) * b + c) • v) := by
  vector_simp


Conclusion ""

NewTactic vector_simp
NewTheorem vector_smul_assoc
