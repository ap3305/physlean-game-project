import GameServer
import Game.Theorems.Space.Theorems

/--
some description
-/
TacticDoc rw

/--
some description
-/
TacticDoc rfl

/--
some description
-/
TacticDoc rewrite

/--
some description
-/
TacticDoc nth_rewrite

/--
some description
-/
TacticDoc nth_rw

/--
some description
-/
TacticDoc rwa

/--
some description
-/
TacticDoc exact

/--
some description
-/
TacticDoc assumption

/--
some description
-/
TacticDoc apply

/--
some description
-/
TacticDoc all_goals

/--
some description
-/
TacticDoc ext

/--
some description
-/
TacticDoc change

/--
some description
-/
TacticDoc simp

/--
some description
-/
TacticDoc ring

/--
some description
-/
TacticDoc vector_simp






/--
`add_zero a` is a proof that `a + 0 = 0`.
-/
TheoremDoc add_zero as "add_zero" in "ℝ"

/--
`zero_add a` is a proof that `0 + a = 0`.
-/
TheoremDoc zero_add as "zero_add" in "ℝ"

/--
`add_neg_cancel a` is a proof that `a + -a = 0`.
-/
TheoremDoc add_neg_cancel as "add_neg_cancel" in "ℝ"

/--
`neg_add_cancel a` is a proof that `-a + a = 0`.
-/
TheoremDoc neg_add_cancel as "neg_add_cancel" in "ℝ"

/--
`add_comm a b` is a proof that `a + b = b + a`.
-/
TheoremDoc add_comm as "add_comm" in "ℝ"

/--
`add_assoc a b c` is a proof that `(a + b) + c = a + (b + c)` where `(a + b) + c` is also written as `a + b + c` in Lean.
-/
TheoremDoc add_assoc as "add_assoc" in "ℝ"

/--
`mul_add a b c` is a proof that `a * (b + c) = a * b + a * c`.
-/
TheoremDoc mul_add as "mul_add" in "ℝ"

/--
`mul_add a b c` is a proof that `(a + b) * c = a * c + b * c`.
-/
TheoremDoc add_mul as "add_mul" in "ℝ"

/--
`one_mul a` is a proof that `1 * a = a`.
-/
TheoremDoc one_mul as "one_mul" in "ℝ"

/--
`one_mul a` is a proof that `a * 1 = a`.
-/
TheoremDoc mul_one as "mul_one" in "ℝ"

/--
`mul_assoc` is a proof that `(a * b) * c = a * (b * c)` where `(a * b) * c` is also written as `a * b * c` in Lean.
-/
TheoremDoc mul_assoc as "mul_assoc" in "ℝ"




/--
`vector_add_zero v` is a proof that `v + 0 = 0` where `v` is a 3 dimensional vector of type `MySpace` or a 4 dimensional vector of type `MySpacetime`.
-/
TheoremDoc MySpace.vector_add_zero as "vector_add_zero" in "Vectors"

/--
`vector_add_inv v` is a proof that `v + -v = 0` where `v` is a 3 dimensional vector of type `MySpace` or a 4 dimensional vector of type `MySpacetime`.
-/
TheoremDoc MySpace.vector_add_inv as "vector_add_inv" in "Vectors"

/--
`vector_add_comm u v` is a proof that `u + v = v + u` where `u v w` are 3 dimensional vectors of type `MySpace` or 4 dimensional vectors of type `MySpacetime`.
-/
TheoremDoc MySpace.vector_add_comm as "vector_add_comm" in "Vectors"

/--
`vector_add_assoc u v w` is a proof that `(u + v) + w = u + (v + w)` where `(u + v) + w` is also written as `u + v + w` in Lean.
`u v w` are 3 dimensional vectors of type `MySpace` or 4 dimensional vectors of type `MySpacetime`.
-/
TheoremDoc MySpace.vector_add_assoc as "vector_add_assoc" in "Vectors"

/--
`vector_smul_one u` is a proof that `1 • u = u` where `u` is a 3 dimensional vector of type `MySpace` or a 4 dimensional vector of type `MySpacetime`.
-/
TheoremDoc MySpace.vector_smul_one as "vector_smul_one" in "Vectors"

/--
`vector_smul_add u v a` is a proof that `a • (u + v) = a • u + a • v` where `u v` are 3 dimensional vectors of type `MySpace` or 4 dimensional vectors of type `MySpacetime`, and `a` is a real number.
-/
TheoremDoc MySpace.vector_smul_add as "vector_smul_add" in "Vectors"

/--
`vector_add_smul u a b` is a proof that `(a + b) • u = a • u + b • u` where `u` is a 3 dimensional vector of type `MySpace` or a 4 dimensional vector of type `MySpacetime`, and `a b` are real numbers.
-/
TheoremDoc MySpace.vector_add_smul as "vector_add_smul" in "Vectors"

/--
`vector_smul_assoc u a b` is a proof that `a • (b • u) = (a * b) • u`.
`u` is a 3 dimensional vector of type `MySpace` or a 4 dimensional vector of type `MySpacetime`, and `a b` are real numbers.
-/
TheoremDoc MySpace.vector_smul_assoc as "vector_smul_assoc" in "Vectors"





/--
`MySpace` is a type representing a 3 dimension vector.
- `v : MySpace` creates a vector `v`.
- `v := { x := 1, y := 2, z := 3 }` assigns values to `v` which can be accessed with `v.x`, `v.y`, and `v.z`.
-/
DefinitionDoc MySpace as "MySpace"
