import Game.Metadata
import Game.Theorems.Inner_Product.Theorems
import Game.Theorems.Inner_Product.TheoremDocs

World "Inner_Product"
Level 4

Title ""

Introduction ""

open my_inner

Statement (u v : MySpace) : ≪u + v, u + v≫ = ≪u, u≫ + 2 * ≪u, v≫ + ≪v, v≫ := by
  rw [inner_add, add_inner, add_inner]
  nth_rewrite 2 [inner_comm]
  ring

Conclusion ""

NewTheorem my_inner.inner_neg
