import Game.Metadata
import Game.TheoremDocs
import Mathlib.Algebra.Ring.Basic
import PhysLean.Units.Dimension
import PhysLean.Units.WithDim.Basic
import PhysLean.Units.WithDim.Area
import PhysLean.Units.UnitDependent

World "UnitWorld"
Level 1

Title "πr^2"

Introduction "Introduce what a dimension is and simp?"

Statement (Area Length : Dimension) (h : Area = ⟨2, 0, 0, 0, 0⟩) (g : Length = ⟨1, 0, 0, 0, 0⟩) : Area = Length^2 := by
  Hint "Start with `ext` to split this goal into a seperate goal for each dimension"
  ext
  Hint "Use `rw [h]` and `rw [g]` to substitute the values of each dimension."
  rw [h, g]
  Hint "Use `simp` to let Lean prove this for you, this works because PhysLean has already defined what it means to take a power of a dimension."
  simp
  Hint "We can add `all_goals` to the start of a command to do the same thing to every active goal, use this to finish the proof."
  all_goals rw [h, g]
  all_goals simp
/-
Statement (x y : Nat) (h : x = 2) (g: y = 4) : x + x = y := by
  Hint "You can either start using `{h}` or `{g}`."
  Branch
    rw [g]
    Hint "You should use `{h}` now."
    rw [h]
  rw [h]
  Hint "You should use `{g}` now."
  rw [g]
-/

Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/



NewTactic rw rfl ext simp
NewDefinition Area Length
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
