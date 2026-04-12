import Game.Metadata
import Game.Theorems.Spacetime.Theorems
import Game.Theorems.Spacetime.TheoremDocs

World "Spacetime"
Level 3

Title ""

Introduction ""

open MySpacetime MySpacetime.CausalCharacter

Statement (u : MySpacetime) (h: ¬(u.causalCharacter = timeLike)) (g: ¬(u.causalCharacter = spaceLike)) : u.causalCharacter = lightLike := by
  rw [causalCharacter]
  split_ifs
  rfl
  all_goals
    rw [causalCharacter] at *
    split_ifs at *
    contradiction

Conclusion ""
