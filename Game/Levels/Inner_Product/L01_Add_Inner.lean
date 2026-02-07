import Game.Metadata
import Game.Theorems.Inner_Product.Theorems
import Game.Theorems.Inner_Product.TheoremDocs

World "Inner_Product"
Level 1

Title ""

Introduction ""

open inner_product

Statement (u v w : MySpace) : my_inner (u + v) w = ≪u, w≫ + ≪v, w≫ := by
  rw [inner_comm]
  rw [inner_add]
  rw [inner_comm]
  nth_rewrite 2 [inner_comm]
  rfl

Conclusion ""

NewTheorem inner_comm inner_add inner_smul
NewDefinition my_inner
