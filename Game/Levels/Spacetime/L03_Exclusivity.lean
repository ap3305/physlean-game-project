import Game.Metadata
import Game.Theorems.Spacetime.Theorems
import Game.Theorems.Spacetime.TheoremDocs

World "Spacetime"
Level 3

Title ""

Introduction ""

open MySpacetime MySpacetime.CausalCharacter

Statement (u : MySpacetime) (h: ¬(u.causalCharacter = timeLike)) (g: ¬(u.causalCharacter = spaceLike)) : u.causalCharacter = lightLike := by
  cases f : u.causalCharacter
  all_goals simp
  exact h f
  exact g f

Conclusion ""
