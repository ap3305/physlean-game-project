import Game.Metadata
import Game.Theorems.Spacetime.Theorems
import Game.Theorems.Spacetime.TheoremDocs
import Game.Theorems.Bilinear.Theorems
import Game.Theorems.Time.Theorems

World "Spacetime"
Level 1

Title "Minkowski Product"

Introduction "Our new definition of `MyBilinear` follows the Minkowski Product which is, as you're about to see, `u.t * v.t - u.x * v.x - u.y * v.y - u.z * v.z`.

To be able to apply all the things we proved in the bilinear world in this new context we first have to show that that \"axioms\" we assumed at the start of that world hold for our new definition."

open MySpacetime

Statement (
  preamble :=
    constructor
    constructor
) (u v w : MySpacetime) (a : ℝ) : ((≪u, v≫ = ≪v, u≫) ∧ (≪u, v + w≫ = ≪u, v≫ + ≪u, w≫)) ∧ (≪a • u, v≫ = a * ≪u, v≫) := by
  all_goals unfold MyBilinear
  ring
  all_goals
    simp
    ring

Conclusion ""


NewDefinition MySpacetime
