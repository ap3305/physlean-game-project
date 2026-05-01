import GameServer
import Game.Theorems.Spacetime.Theorems








/--
`MySpacetime` is a type representing a 1 dimension vector.
- `v : MySpacetime` represents a vector `v` of type `MySpacetime`.
- `v := { space = ?, time = ? }` assigns values of type `MySpace` and `MyTime` to `v` which can be accessed with `v.space` and `v.time`.
- The values held within `v.space` and `v.time` can be accessed using `v.space.x`, `v.space.y`, `v.space.z`, and `v.time.val` directly or using `v.x`, `v.y`, `v.z`, and `v.t`.
- `v.causalCharacter` holds a value of `spaceLike`, `lightLike`, or `spaceLike` depending on whether `≪v, v≫` is negative, zero, or positive respectively.
-/

DefinitionDoc MySpacetime as "MySpacetime"
