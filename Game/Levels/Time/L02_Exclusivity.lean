import Game.Metadata
import Game.Theorems.Time.Theorems
import Game.Theorems.Time.TheoremDocs

World "Time"
Level 2

Title ""

Introduction ""

Statement (t : MyTime) (h: is_present t = True) : ¬(is_past t ∨ is_future t) := by
  rw [is_past, is_future]
  rw [is_present] at h
  simp at h
  simp
  rw [h]



Conclusion ""
