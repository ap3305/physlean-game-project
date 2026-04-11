import Game.Metadata
import Game.Theorems.Time.Theorems
import Game.Theorems.Time.TheoremDocs

World "Time"
Level 2

Title ""

Introduction ""

open MyTime MyTime.TimeCharacter

Statement (t : MyTime) (h: ¬(t.timeCharacter = past)) (g: ¬(t.timeCharacter = future)) : t.timeCharacter = present := by
  cases f : t.timeCharacter
  all_goals simp
  exact h f
  exact g f


Conclusion ""
