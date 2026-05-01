import Game.Metadata
import Game.Theorems.Bilinear.Theorems
import Game.Theorems.Bilinear.TheoremDocs

World "Bilinear"
Level 4

Title "bilinear_self"

Introduction ""

open MyBilinear

Statement (u v : MySpace) : ≪u + v, u + v≫ = ≪u, u≫ + 2 * ≪u, v≫ + ≪v, v≫ := by
  rw [bilinear_add, add_bilinear, add_bilinear]
  nth_rewrite 2 [bilinear_comm]
  ring

Conclusion "That's the Bilinear World done, short but sweet! Now you can either finish the Time World or move on to the Spacetime World if you've done that already! Exciting!"

NewTheorem MyBilinear.bilinear_neg
