import Game.Metadata
import Game.Theorems
import Game.TheoremDocs
import Mathlib.Algebra.Ring.Basic
import PhysLean.Units.Dimension
import PhysLean.Units.UnitDependent

World "UnitWorld"
Level 2

Title "Need for Speed"

Introduction "Introduce what a dimension is and simp?"

Statement (VelocityDim : Dimension) (h : VelocityDim = _root_.LengthDim / _root_.TimeDim) : VelocityDim = ⟨1, -1, 0, 0, 0⟩ := by
  rw [h]
  Hint "Start with `ext` to split this goal into a seperate goal for each dimension"
  ext
  rw [LengthDim, TimeDim]
  simp
  Hint "We can add `all_goals` to the start of a command to do the same thing to every active goal, use this to finish the proof."
  all_goals rw [LengthDim, TimeDim]
  all_goals simp

Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

NewTactic ext all_goals
NewDefinition AreaDim TimeDim
