import Game.Metadata
import Game.Theorems
import Game.TheoremDocs
import Mathlib.Algebra.Ring.Basic
import PhysLean.Units.Dimension
import PhysLean.Units.UnitDependent

World "UnitWorld"
Level 3

Title "Getting Energised"

Introduction "Introduce what a dimension is and simp?"

Statement (EnergyDim : Dimension) (h : EnergyDim = _root_.MassDim * VelocityDim ^ 2) : EnergyDim = ⟨2, -2, 1, 0, 0⟩ := by
  rw [h]
  ext
  all_goals rw [MassDim, VelocityDim]
  all_goals simp


Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

NewDefinition VelocityDim MassDim
