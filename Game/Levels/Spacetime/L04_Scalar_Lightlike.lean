import Game.Metadata
import Game.Theorems.Spacetime.Theorems
import Game.Theorems.Spacetime.TheoremDocs

World "Spacetime"
Level 4

Title ""

Introduction ""

open MySpacetime MySpacetime.CausalCharacter

Statement (u v : MySpacetime) (a : ℝ) (h: u = a • v) (g: v.causalCharacter = lightLike) : u.causalCharacter = lightLike := by
  rw [causalCharacter] at g
  split at g
  rename_i hv
  rw [h]
  rw [causalCharacter]
  bilinear_simp
  rw [hv]
  ring
  simp
  split at g
  contradiction
  contradiction

Conclusion ""
