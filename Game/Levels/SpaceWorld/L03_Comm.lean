import Game.Metadata
import Game.Theorems
import Game.TheoremDocs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic

World "SpaceWorld"
Level 3

Title "Back and Forth"

Introduction ""

Statement (u v : space) (h : u = ![1, 2, 3]) (g : v = ![3, 4, 5]) : u + v = v + u := by
  rw[h, g]
  ext
  all_goals
    simp
    ring

Conclusion ""

NewTactic ext all_goals
NewTheorem vector_add_zero
