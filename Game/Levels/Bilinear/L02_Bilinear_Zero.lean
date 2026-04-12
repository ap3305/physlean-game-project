import Game.Metadata
import Game.Theorems.Bilinear.Theorems
import Game.Theorems.Bilinear.TheoremDocs

World "Bilinear"
Level 2

Title ""

Introduction ""

open MyBilinear

Statement (
  preamble :=
    constructor
    have h : ≪v, 0≫ = ≪v, 0 + 0≫ := by simp_vector
    rotate_right
) (v : MySpace) : (≪v, 0≫ = 0) ∧ (≪v, 0≫ = ≪v, 0+0≫) := by
  simp_vector
  rw [bilinear_add] at h
  nth_rw 1 [← add_zero ≪v, 0≫] at h
  simp at h
  exact h

Conclusion ""

NewTheorem MyBilinear.add_bilinear MyBilinear.smul_bilinear
