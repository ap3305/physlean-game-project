import Game.Metadata
import Game.Theorems.Space.Theorems
import Game.Theorems.Space.TheoremDocs
import Mathlib.Tactic.Abel

World "Space"
Level 9

Title "simp_vector"

Introduction "Let's put everything we just proved into one place. `simp_vector` is a macro which uses `simp` combined with the theorems we just proved to solve any goal involving `MySpace`, `+`, and `•`. Isn't that neat.

This homegrown tactic is defined as such:
```
macro \"simp_vector\" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [
  vector_add_zero, vector_add_inv, vector_add_comm, vector_add_assoc,
  vector_smul_one, vector_smul_add, ← vector_add_smul, vector_smul_assoc,
] $(loc)? <;> ring <;> simp only [vector_add_comm]
)
```
There's a little bit of syntactical soup involved but isn't that neat?"

open MySpace

Statement (u v : MySpace) (a b c : ℝ) : (a * b) • (c • u + v) + (a * (b + c)) • v = a • ((b * c) • u + ((2 : ℝ) * b + c) • v) := by
  simp_vector


Conclusion "And that's the end of Space World! Now you can either visit the Bilinear World to learn some new concepts or the Time World to learn some new tactics."

NewTactic simp_vector
NewTheorem MySpace.vector_smul_assoc
