import Game.Metadata
import Game.Theorems.Space.Theorems
import Game.Theorems.Space.TheoremDocs

World "Space"
Level 1

Title ""

Introduction ""

Statement (v : MySpace) : v + (0 : MySpace) = v := by
  ext
  change v.x + 0 = v.x
  rw [add_zero]
  change v.y + 0 = v.y
  rw [add_zero]
  change v.z + 0 = v.z
  rw [add_zero]

Conclusion ""

NewTactic ext rw change rfl exact apply
NewTheorem add_zero zero_add
NewDefinition MySpace

NewHiddenTactic rewrite nth_rewrite rwa
