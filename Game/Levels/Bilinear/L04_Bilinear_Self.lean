import Game.Metadata
import Game.Theorems.Bilinear.Theorems
import Game.Theorems.Bilinear.TheoremDocs

World "Bilinear"
Level 4

Title ""

Introduction ""

open my_bilinear

Statement (u v : MySpace) : ≪u + v, u + v≫ = ≪u, u≫ + 2 * ≪u, v≫ + ≪v, v≫ := by
  rw [bilinear_add, add_bilinear, add_bilinear]
  nth_rewrite 2 [bilinear_comm]
  ring

Conclusion ""

NewTheorem my_bilinear.bilinear_neg
