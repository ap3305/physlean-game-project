import Game.Metadata
import Game.Theorems.Time.Theorems
import Game.Theorems.Time.TheoremDocs

World "Time"
Level 1

Title ""

Introduction ""

open MyTime

Statement (t : MyTime) (h: t.val = 4): t.is_future := by
  rw [is_future]
  rw [h]
  norm_num


Conclusion ""

NewTactic norm_num
NewTheorem MyTime.is_past MyTime.is_present MyTime.is_future
NewDefinition MyTime
