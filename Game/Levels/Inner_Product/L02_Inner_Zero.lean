import Game.Metadata
import Game.Theorems.Inner_Product.Theorems
import Game.Theorems.Inner_Product.TheoremDocs

World "Inner_Product"
Level 2

Title ""

Introduction ""

Statement (
  preamble :=
    constructor
    have h : ≪v, 0≫ = ≪v, 0 + 0≫ := by vector_simp
    rotate_right
) (v : MySpace) : (≪v, 0≫ = 0) ∧ (≪v, 0≫ = ≪v, 0+0≫) := by
  vector_simp
  rw [add_inner] at h
  nth_rw 1 [← add_zero ≪v, 0≫] at h
  simp at h
  exact h

Conclusion ""

NewTheorem add_inner
