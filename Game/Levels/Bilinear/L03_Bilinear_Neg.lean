import Game.Metadata
import Game.Theorems.Bilinear.Theorems
import Game.Theorems.Bilinear.TheoremDocs

World "Bilinear"
Level 3

Title ""

Introduction ""

open MyBilinear

Statement (
  preamble :=
    constructor
    have h : -v = (-1 : ℝ) • v := by ext <;> simp
    rotate_right
) (u v : MySpace) : (≪u, -v≫ = -≪u, v≫) ∧ (-v = (-1 : ℝ) • v) := by
  ext
  simp
  simp
  simp
  rw [h]
  rw [bilinear_smul]
  ring

Conclusion ""

NewTheorem MyBilinear.bilinear_zero
