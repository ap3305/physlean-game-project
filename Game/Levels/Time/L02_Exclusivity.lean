import Game.Metadata
import Game.Theorems.Time.Theorems
import Game.Theorems.Time.TheoremDocs

World "Time"
Level 2

Title ""

Introduction ""

open MyTime MyTime.TimeCharacter

Statement (t : MyTime) (h: ¬(t.timeCharacter = past)) (g: ¬(t.timeCharacter = future)) : t.timeCharacter = present := by
  rw [timeCharacter]
  split_ifs
  rfl
  Branch
    rw [timeCharacter] at g
    split_ifs at g
    contradiction
    rw [timeCharacter] at h
    split_ifs at h
    contradiction
  all_goals
    rw [timeCharacter] at *
    split_ifs at *
    contradiction


Conclusion ""

NewTactic split_ifs contradiction
DisabledTactic simp
