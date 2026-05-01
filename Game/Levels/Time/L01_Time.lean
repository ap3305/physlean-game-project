import Game.Metadata
import Game.Theorems.Time.Theorems
import Game.Theorems.Time.TheoremDocs

World "Time"
Level 1

Title "MyTime"

Introduction "Vectors of type `MyTime` not only hold their value but also a `timeCharacter`. We can access this value using `rw[timeCharacter]` and then collapsing the if statement involved.
One way to do this is using `norm_num`, you can think of it as a more powerful version but more specific version of `ring`."

open MyTime MyTime.TimeCharacter

Statement (t : MyTime) (h: t.val = 4): t.timeCharacter = future := by
  rw [timeCharacter]
  rw [h]
  norm_num


Conclusion ""

NewTactic norm_num
NewDefinition MyTime
