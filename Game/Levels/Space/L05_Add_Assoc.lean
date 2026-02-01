import Game.Metadata
import Game.Theorems.Space.Theorems
import Game.Theorems.Space.TheoremDocs

World "Space"
Level 5

Title ""

Introduction ""

Statement (u v w : space) (h : u = ![1, 2, 3]) (g : v = ![3, 4, 5]) (f : w = ![5, 6, 7]) : u + (v + w) = (u + v) + w := by
  rw [h, g, f]
  ext
  all_goals
    simp
    ring

Conclusion ""
