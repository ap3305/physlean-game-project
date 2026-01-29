import Game.Metadata
import Game.Theorems
import Game.TheoremDocs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Geometry.Manifold.Diffeomorph
import PhysLean.Units.Basic
import PhysLean.Units.Dimension
import PhysLean.Units.UnitDependent
import PhysLean.SpaceAndTime.Space.LengthUnit

World "UnitWorld"
Level 4

Title ""

Introduction ""

def LengthType : Type := Dimensionful (WithDim LengthDim ℝ)
def TimeType : Type := Dimensionful (WithDim TimeDim ℝ)

noncomputable def meter : LengthType := CarriesDimension.toDimensionful UnitChoices.SI ⟨1⟩
noncomputable def second : TimeType := CarriesDimension.toDimensionful UnitChoices.SI ⟨1⟩

#eval LengthUnit.meters.val

Statement : 1 + 1  = 2 := by
  rfl


Conclusion ""

NewDefinition EnergyDim
