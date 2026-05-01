import GameServer
import Game.Theorems.Bilinear.Theorems




/--
`bilinear_comm u v` is a proof that `≪u, v≫ = ≪v, u≫`.
-/
TheoremDoc MyBilinear.bilinear_comm as "bilinear_comm" in "Bilinear"

/--
`bilinear_add u v w` is a proof that `≪u, v + w≫ = ≪u, v≫ + ≪u, w≫`.
-/
TheoremDoc MyBilinear.bilinear_add as "bilinear_add" in "Bilinear"

/--
`bilinear_smul u v a` is a proof that `≪u, a • v≫ = a * ≪u, v≫`.
-/
TheoremDoc MyBilinear.bilinear_smul as "bilinear_smul" in "Bilinear"

/--
`add_bilinear u v w` is a proof that `≪u + v, w≫ = ≪u, w≫ + ≪v, w≫`.
-/
TheoremDoc MyBilinear.add_bilinear as "add_bilinear" in "Bilinear"

/--
`smul_bilinear u v a` is a proof that `≪a • u, v≫ = a * ≪u, v≫`.
-/
TheoremDoc MyBilinear.smul_bilinear as "smul_bilinear" in "Bilinear"

/--
`bilinear_zero v` is a proof that `≪v, 0≫ = 0`.
-/
TheoremDoc MyBilinear.bilinear_zero as "bilinear_zero" in "Bilinear"

/--
`bilinear_self_add u v` is a proof that `≪u + v, u + v≫ = ≪u, u≫ + 2 * ≪u, v≫ + ≪v, v≫`.
-/
TheoremDoc MyBilinear.bilinear_self_add as "bilinear_self_add" in "Bilinear"

/--
`bilinear_neg u v` is a proof that `≪u, -v≫ = -≪u, v≫`.
-/
TheoremDoc MyBilinear.bilinear_neg as "bilinear_neg" in "Bilinear"



/--
`MyBilinear` is a type that is first defined as taking in two arguments of type `MySpace` with an output of type `ℝ`.

In later worlds, `MyBilinear` is taken to be the Minkowski Product is defined as follows:
```def MyBilinear (u v : MySpacetime) : ℝ := u.t * v.t - u.x * v.x - u.y * v.y - u.z * v.z```

In both instances `MyBilinear` can either be written as `MyBilinear u v` or `≪u, v≫`.
-/
DefinitionDoc MyBilinear.MyBilinear as "MyBilinear"
