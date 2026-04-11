import Game.Metadata
import Game.Theorems.Time.Theorems
import Game.Theorems.Time.TheoremDocs

World "Time"
Level 1

Title ""

Introduction ""

open MyTime MyTime.TimeCharacter

Statement (t : MyTime) (h: t.val = 4): t.timeCharacter = future := by
  rw [timeCharacter]
  rw [h]
  norm_num


Conclusion ""

NewTactic norm_num
NewDefinition MyTime
