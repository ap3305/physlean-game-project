import Game.Metadata
import Game.Theorems.Spacetime.Theorems
import Game.Theorems.Spacetime.TheoremDocs

World "Spacetime"
Level 2

Title "causalCharacter"

Introduction "Assume to be 1 unit of space per unit of time"

open MySpacetime MySpacetime.CausalCharacter

Statement (u : MySpacetime) (h: u = { time := ⟨1⟩, space := ⟨1, 0, 0⟩ }) : u.causalCharacter = lightLike := by
  rw [causalCharacter]
  rw [h]
  simp

Conclusion ""
