import Game.Metadata
import Game.Theorems.Time.Theorems
import Game.Theorems.Time.TheoremDocs

World "Time"
Level 1

Title ""

Introduction ""

Statement (t : MyTime) (h: t.val = 4): is_future t := by
  rw [is_future]
  rw [h]
  norm_num


Conclusion ""

NewTactic norm_num
NewTheorem is_past is_present is_future
NewDefinition MyTime
