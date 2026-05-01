import Game.Metadata
import Game.Theorems.Time.Theorems
import Game.Theorems.Time.TheoremDocs

World "Time"
Level 2

Title "Exclusivity"

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
    Hint "Good job! As you're tackling this second goal do you think there's a way you could've solved both goals at the same time? It might be useful to know that $*$ means \"all\" in Lean"
    rw [timeCharacter] at h
    split_ifs at h
    contradiction
  all_goals
    rw [timeCharacter] at *
    Hint "Nice going, can you finish the level in just two more lines?"
    split_ifs at *
    contradiction


Conclusion ""

NewTactic split_ifs contradiction
DisabledTactic simp
