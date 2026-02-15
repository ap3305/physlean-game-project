import Game.Metadata
import Game.Theorems.Bilinear.Theorems
import Game.Theorems.Bilinear.TheoremDocs

World "Bilinear"
Level 1

Title ""

Introduction ""

open my_bilinear

Statement (u v w : MySpace) : my_bilinear (u + v) w = ≪u, w≫ + ≪v, w≫ := by
  rw [bilinear_comm]
  rw [bilinear_add]
  rw [bilinear_comm]
  nth_rewrite 2 [bilinear_comm]
  rfl

Conclusion ""

NewTheorem my_bilinear.bilinear_comm my_bilinear.bilinear_add my_bilinear.bilinear_smul
NewDefinition my_bilinear.my_bilinear
