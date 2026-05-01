import GameServer
import Game.Theorems.Time.Theorems

/--
`norm_num` can be thought about as a more powerful but more limited version of `ring`. It will solve any arithmetic expressive involving `+`, `-`, `*`, `^`, or `≤`.
-/
TacticDoc norm_num




/--
`MyTime` is a type representing a 1 dimension vector.
- `v : MyTime` represents a vector `v` of type `MyTime`.
- `v := { val = ? }` assigns a value of type `ℝ` to `v` which can be accessed with `v.val`.
- `v.timeCharacter` holds a value of `past`, `present`, or `future` depending on whether `v.val` is negative, zero, or positive respectively.
-/
DefinitionDoc MyTime as "MyTime"
