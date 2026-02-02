import Game.Metadata
import Game.Theorems.Space.Theorems
import Game.Theorems.Space.TheoremDocs

World "Space"
Level 1

Title "Humble Beginnings"

Introduction "In Physlean, `Space (d : ℕ)` is a type representing a d-dimensional space. In this world we are specifically working with 3 dimensions so we define `abbrev space : Type := Space 3`. This locks us into working in three dimensions whilst maintaing access to all of the results Physlean provides about `Space`.

Mathlib provides us with notation for creating vectors of any length using the constructor `![a, b, ...]`.

We addionally define `space.x`, `space.y`, and `space.z` and three lemmas `x_val`, `y_val`, and `z_val` equating them to the values `![x, y, z]`, use this level to familarise yourself with all of this notation."

Statement (u v : Space) (h : u = ⟨1, 2, 3⟩) (g : v = ⟨3, 4, 5⟩) : u.x + v.z = u.y * v.x := by
  rw [h, g]
  change 1 + 5 = 2 * 3
  ring

Conclusion ""

NewTactic rw change ring rfl
NewDefinition Space

NewHiddenTactic rewrite nth_rewrite rwa
