import Game.Metadata
import Game.Theorems.Bilinear.Theorems
import Game.Theorems.Bilinear.TheoremDocs

World "Bilinear"
Level 1

Title "add_bilinear"

Introduction "In order to kick us off, we assume three properties of `MyBilinear`, our bilinear product: `bilinear_comm`, `bilinear_add`, and `bilinear_smul`. Be sure to give them a read!

Additionally, we make things easier by defining some custom syntax for this operation:
```
notation \"≪\" u \", \" v \"≫\" => MyBilinear u v
```"

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
