import Game.Metadata
import Game.Theorems.Space.Theorems
import Game.Theorems.Space.TheoremDocs

World "Space"
Level 6

Title ""

Introduction "Define `dot_product`, make notation for it using `infix:100 \" • \" => dot_product`, 100 is precedence."

Statement (u v : space) (a : ℝ) (h : u = ![1, 2, 3]) (g : v = ![3, 4, 5]) : a * (u + v) = a * u + a * v := by
  rw [h, g]

Conclusion ""
