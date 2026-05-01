import Game.Metadata
import Game.Theorems.Spacetime.Theorems
import Game.Theorems.Spacetime.TheoremDocs

World "Spacetime"
Level 2

Title "causalCharacter"

Introduction "You might recognise some of these next few levels from a previous world. Hmmm, probably just a coincidence.

Either way it may be helpful to know that the `causalCharacter` is based on the sign of the Minkowski product of a vector with itself. While in the real world this also has an added step to account for units, here we assume `c = 1` and everything works out great!"

open MySpacetime MySpacetime.CausalCharacter

Statement (u : MySpacetime) (h: u = { time := ⟨1⟩, space := ⟨1, 0, 0⟩ }) : u.causalCharacter = lightLike := by
  rw [causalCharacter]
  rw [h]
  simp

Conclusion ""
