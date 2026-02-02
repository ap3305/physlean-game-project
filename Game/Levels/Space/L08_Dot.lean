import Game.Metadata
import Game.Theorems.Space.Theorems
import Game.Theorems.Space.TheoremDocs

World "Space"
Level 8

Title ""

Introduction "Define `dot_product`, make notation for it using `infix:100 \" • \" => dot_product`, 100 is precedence."

Statement (u v : Space) (h : u = ⟨1, 2, 3⟩) (g : v = ⟨3, 4, 5⟩) : u • v = 26 := by
  rw [h, g]
  simp
  ring

Conclusion ""

NewDefinition dot_product
