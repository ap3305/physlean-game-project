import Game.Metadata
import Game.Theorems.Spacetime.Theorems
import Game.Theorems.Spacetime.TheoremDocs

World "Spacetime"
Level 1

Title ""

Introduction ""

open MySpacetime

Statement (
  preamble :=
    constructor
    constructor
) (u v w : MySpacetime) (a : ℝ) : ((≪u, v≫ = ≪v, u≫) ∧ (≪u, v + w≫ = ≪u, v≫ + ≪u, w≫)) ∧ (≪a • u, v≫ = a * ≪u, v≫) := by
  rw [my_bilinear]
  rw [my_bilinear]
  ring
  rw [my_bilinear]
  rw [my_bilinear]
  rw [my_bilinear]
  simp
  ring
  rw [my_bilinear]
  rw [my_bilinear]
  simp
  ring

Conclusion ""


NewDefinition MySpacetime
