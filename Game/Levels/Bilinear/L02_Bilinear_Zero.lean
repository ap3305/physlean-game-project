import Game.Metadata
import Game.Theorems.Bilinear.Theorems
import Game.Theorems.Bilinear.TheoremDocs

World "Bilinear"
Level 2

Title "bilinear_zero"

Introduction "In this level you have two goals, after you prove the first one you will be able to use it in the second.

Or if you feel like it you could skip right to the second, whatever works."

open MyBilinear

Statement (
  preamble :=
    constructor
    have h : ≪v, 0≫ = ≪v, 0 + 0≫ := by simp_vector
    rotate_right
) (v : MySpace) : (≪v, 0≫ = 0) ∧ (≪v, 0≫ = ≪v, 0+0≫) := by
  simp_vector
  Hint (hidden := true) "It may be useful to make sure you're confident with how nth_rw works. If you're not sure check the documentation for rw."
  rw [bilinear_add] at h
  nth_rw 1 [← add_zero ≪v, 0≫] at h
  simp at h
  exact h

Conclusion ""

NewTheorem MyBilinear.add_bilinear MyBilinear.smul_bilinear
