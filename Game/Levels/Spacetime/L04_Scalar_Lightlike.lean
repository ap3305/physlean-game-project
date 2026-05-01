import Game.Metadata
import Game.Theorems.Spacetime.Theorems
import Game.Theorems.Spacetime.TheoremDocs

World "Spacetime"
Level 4

Title "Scalar lightLike"

Introduction ""

open MySpacetime MySpacetime.CausalCharacter

Statement (u v : MySpacetime) (a : ℝ) (h: u = a • v) (g: v.causalCharacter = lightLike) : u.causalCharacter = lightLike := by
  Hint (hidden := true) "If you're stuck have a look at what you did in level 3 in the Light World."
  rw [causalCharacter]
  split_ifs
  rfl
  all_goals
    rw [causalCharacter] at g
    split_ifs at g
    rename_i ha hb hc
    rw [h] at ha
    repeat rw [bilinear_comm, bilinear_smul] at ha
    rw [hc] at ha
    norm_num at ha

Conclusion ""
