import GameServer
import Game.Theorems.Time.Theorems

/--
`norm_num` can be thought about as a more powerful but more limited version of `ring`. It will solve any arithmetic expressive involving `+`, `-`, `*`, `^`, or `≤`.
-/
TacticDoc norm_num

/--
`split_ifs` splits an `if then else` statement into a goal for each outcome.

Be warned, `split_ifs` may create hypotheses which are inaccessible that you would like to use. Should this happen you should turn to `rename i`.
-/
TacticDoc split_ifs

/--
`contradiction` will solve a goal if two hypothoseis directly contradict each other or if one hypothosis is `false`. For example `h: false` or `h: a` and `g: ¬a`.
-/
TacticDoc contradiction

/--
`rename_i` allows you give names to hypotheses which are normally inaccessible, such as those created by `split_ifs`.
-/
TacticDoc rename_i


/--
`MyTime` is a type representing a 1 dimension vector.
- `v : MyTime` represents a vector `v` of type `MyTime`.
- `v := { val = ? }` assigns a value of type `ℝ` to `v` which can be accessed with `v.val`.
- `v.timeCharacter` holds a value of `past`, `present`, or `future` depending on whether `v.val` is negative, zero, or positive respectively.
-/
DefinitionDoc MyTime as "MyTime"
