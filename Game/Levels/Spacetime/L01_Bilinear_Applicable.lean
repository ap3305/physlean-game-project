import Game.Metadata
import Game.Theorems.Spacetime.Theorems
import Game.Theorems.Spacetime.TheoremDocs
import Game.Theorems.Bilinear.Theorems
import Game.Theorems.Time.Theorems

World "Spacetime"
Level 1

Title ""

Introduction ""

theorem world_dependant (u v : MySpace) (t : MyTime) : True := by simp

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
