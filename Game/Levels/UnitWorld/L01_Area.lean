import Game.Metadata
import Game.Theorems
import Game.TheoremDocs
import Mathlib.Algebra.Ring.Basic
import PhysLean.Units.Dimension
import PhysLean.Units.UnitDependent

World "UnitWorld"
Level 1

Title "πr^2"

Introduction "Introduce what a dimension is and simp?"

Statement (AreaDim : Dimension) (h : AreaDim = LengthDim ^ 2) : AreaDim.length = 2 := by
  Hint "Use `rw [h]` to substitute."
  rw [h]
  Hint "Use `simp` to let Lean prove this for you, this works because PhysLean has already defined what it means to take a power of a dimension."
  simp
  rfl


Conclusion "This last message appears if the level is solved."

NewTactic rw rfl simp
NewDefinition LengthDim
