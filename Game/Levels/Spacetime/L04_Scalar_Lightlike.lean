import Game.Metadata
import Game.Theorems.Spacetime.Theorems
import Game.Theorems.Spacetime.TheoremDocs

World "Spacetime"
Level 4

Title ""

Introduction ""

open MySpacetime MySpacetime.CausalCharacter

Statement (u v : MySpacetime) (a : ℝ) (h: u = a • v) (g: v.causalCharacter = lightLike) : u.causalCharacter = lightLike := by
  rw [causalCharacter]
  split_ifs
  rfl
  all_goals
    rw [causalCharacter] at g
    split_ifs at g
    rename_i ha hb hc
    rw [h] at ha
    simp_bilinear at ha
    rw [hc] at ha
    norm_num at ha

Conclusion ""
