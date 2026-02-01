import Game.Metadata
import Game.Theorems.Space.Theorems
import Game.Theorems.Space.TheoremDocs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic

World "Space"
Level 6

Title ""

Introduction "Define `dot_product`, make notation for it using `infix:100 \" • \" => dot_product`, 100 is precedence."

Statement (u v : space) (h : u = ![1, 2, 3]) (g : v = ![3, 4, 5]) : u • v = 26 := by
  rw [h, g]
  simp
  ring

Conclusion ""

NewDefinition dot_product
