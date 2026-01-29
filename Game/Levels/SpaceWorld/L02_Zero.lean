import Game.Metadata
import Game.Theorems
import Game.TheoremDocs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic

World "SpaceWorld"
Level 2

Title ""

Introduction ""

Statement (u v : space) (h : u = ![1, 2, 3]) : u + 0 = u := by
  rw [h]
  ext
  all_goals
    simp

Conclusion ""

NewTactic ext all_goals
