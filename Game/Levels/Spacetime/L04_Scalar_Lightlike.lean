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

Conclusion "Wow! That's it! That's the game! As it stands at least. If you're interested in learning more about PhysLean be sure to check out the website and if you're super keen you can find out how to get involved in the project yourself at https://physlib.io/GetInvolved.html.

Thank you for taking the time to play this game all the way through, I hope you had fun and have a great day!"
