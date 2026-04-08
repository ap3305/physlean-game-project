import Game.Metadata
import Game.Theorems.Bilinear.Theorems
import Game.Theorems.Bilinear.TheoremDocs

World "Bilinear"
Level 1

Title ""

Introduction ""

open MyBilinear

Statement (u v w : MySpace) : MyBilinear (u + v) w = ≪u, w≫ + ≪v, w≫ := by
  rw [bilinear_comm]
  rw [bilinear_add]
  rw [bilinear_comm]
  nth_rewrite 2 [bilinear_comm]
  rfl

Conclusion ""

NewTheorem MyBilinear.bilinear_comm MyBilinear.bilinear_add MyBilinear.bilinear_smul
NewDefinition MyBilinear.MyBilinear
