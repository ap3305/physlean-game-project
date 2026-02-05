import Game.Metadata
import Game.Theorems.Inner_Product.Theorems
import Game.Theorems.Inner_Product.TheoremDocs

World "Inner_Product"
Level 1

Title ""

Introduction ""

Statement (u v w : MySpace) : my_inner u (v + w) = ≪u, v≫ + ≪u, w≫ := by
  rw [inner_comm]
  rw [inner_add]
  rw [inner_comm]
  nth_rewrite 2 [inner_comm]
  rfl

Conclusion ""
