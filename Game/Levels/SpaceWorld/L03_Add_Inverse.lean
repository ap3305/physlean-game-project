import Game.Metadata
import Game.Theorems
import Game.TheoremDocs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic

World "SpaceWorld"
Level 3

Title ""

Introduction "Define `dot_product`, make notation for it using `infix:100 \" • \" => dot_product`, 100 is precedence."

Statement (u : space) (h : u = ![1, 2, 3]) : u + (-u) = 0 := by
  rw [h]
  ext
  all_goals
    simp

Conclusion ""
