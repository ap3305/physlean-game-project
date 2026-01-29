import Game.Metadata
import Game.Theorems
import Game.TheoremDocs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import PhysLean.SpaceAndTime.Space.Basic

World "SpaceWorld"
Level 1

Title ""

Introduction ""

open InnerProductSpace

Statement (u v : Space 3) (h : inner ℝ u v = 0) : ‖u‖^2 + ‖v‖^2 = ‖u + v‖^2 := by
  repeat rw [← real_inner_self_eq_norm_sq]
  rw [inner_add_left]
  repeat rw [inner_add_right]
  rw [real_inner_comm u v]
  repeat rw [h]
  simp


Conclusion ""
