import Game.Metadata
import Game.Theorems.Time.Theorems
import Game.Theorems.Time.TheoremDocs

World "Time"
Level 3

Title "Scalar present"

Introduction "When using `split_ifs` it creates inaccessable assumptions as I'm sure you've seen, but what if we want to access those assumptions?

`rename_i` lets us asign names to these assumptions and use them like any other. The best part is you can rename multiple at the same time! Just use `rename_i ha hb hc ...`."

open MyTime MyTime.TimeCharacter

Statement (t u : MyTime) (a : ℝ) (h: t = a • u) (g: u.timeCharacter = present) : t.timeCharacter = present := by
  rw [timeCharacter]
  split_ifs with ha
  rfl
  all_goals
    rw [timeCharacter] at g
    split_ifs at g
    rename_i hb hc
  rw [h] at hb
  simp at hb
  rw [hc] at hb
  simp at hb
  rw [h] at ha
  simp at ha
  rw [hc] at ha
  simp at ha

Conclusion "Aaaaaand that's time! Or at least that's the Time World done. Time to move on to the next one!"

NewTactic rename_i
