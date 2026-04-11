import Game.Metadata
import Game.Theorems.Time.Theorems
import Game.Theorems.Time.TheoremDocs

World "Time"
Level 2

Title ""

Introduction ""

open MyTime

Statement (t : MyTime) (h: t.is_present = True) : ¬(t.is_past ∨ t.is_future) := by
  rw [is_past, is_future]
  rw [is_present] at h
  simp at h
  simp
  rw [h]



Conclusion ""
