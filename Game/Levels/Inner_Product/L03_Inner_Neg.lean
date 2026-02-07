import Game.Metadata
import Game.Theorems.Inner_Product.Theorems
import Game.Theorems.Inner_Product.TheoremDocs

World "Inner_Product"
Level 3

Title ""

Introduction ""

open inner_product

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
  rw [inner_comm]
  rw [inner_smul]
  norm_num
  rw [inner_comm]


Conclusion ""

NewTheorem inner_zero
