import Game.Metadata
import Game.Theorems.Spacetime.Theorems
import Game.Theorems.Spacetime.TheoremDocs

World "Spacetime"
Level 2

Title ""

Introduction "This level is not yet implemented and is a copy of the previous one"

open MySpacetime

Statement (u v w : MySpacetime) (a : ℝ) :  := by
  rw [MyBilinear]
  rw [MyBilinear]
  ring
  rw [MyBilinear]
  rw [MyBilinear]
  rw [MyBilinear]
  simp
  ring
  rw [MyBilinear]
  rw [MyBilinear]
  simp
  ring

Conclusion ""
