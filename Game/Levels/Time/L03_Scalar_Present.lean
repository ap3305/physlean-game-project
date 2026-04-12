import Game.Metadata
import Game.Theorems.Time.Theorems
import Game.Theorems.Time.TheoremDocs

World "Time"
Level 3

Title ""

Introduction ""

open MyTime MyTime.TimeCharacter

Statement (t u : MyTime) (a : ℝ) (h: t = a • u) (g: u.timeCharacter = present) : t.timeCharacter = present := by
  rw [timeCharacter]
  split_ifs
  rfl
  all_goals
    rw [timeCharacter] at g
    split_ifs at g
    rename_i ha hb hc
  rw [h] at hb
  simp at hb
  rw [hc] at hb
  simp at hb
  rw [h] at ha
  simp at ha
  rw [hc] at ha
  simp at ha

Conclusion ""

NewTactic rename_i
