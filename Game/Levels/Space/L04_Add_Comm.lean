import Game.Metadata
import Game.Theorems.Space.Theorems
import Game.Theorems.Space.TheoremDocs

World "Space"
Level 4

Title "Back and Forth"

Introduction ""

Statement (u v : space) (h : u = ![1, 2, 3]) (g : v = ![3, 4, 5]) : u + v = v + u := by
  rw[h, g]
  ext
  all_goals
    simp
    ring

Conclusion ""

NewTactic ext all_goals
NewTheorem vector_add_zero
