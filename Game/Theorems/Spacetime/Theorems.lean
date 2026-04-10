import GameServer
import Game.Metadata
import Game.Theorems.Space.Theorems
import Game.Theorems.Time.Theorems

@[ext]
structure MySpacetime where
  t : MyTime
  s : MySpace

namespace MySpacetime

instance : Add MySpacetime where
  add u v := { t := u.t + v.t, s := u.s + v.s }

instance : Sub MySpacetime where
  sub u v := { t := u.t - v.t, s := u.s - v.s }

instance : Neg MySpacetime where
  neg u := { t := -u.t, s := -u.s }

instance : SMul ℝ MySpacetime where
  smul a u := { t := a • u.t, s := a • u.s }

instance : Zero MySpacetime where
  zero := { t := 0, s := 0 }


def my_minkowski : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![1, -1, -1, -1]

notation "η" => my_minkowski

def MyBilinear (u v : MySpacetime) : ℝ := u.t.val * v.t.val - u.s.x * v.s.x - u.s.y * v.s.y - u.s.z * v.s.z

notation "≪" u ", " v "≫" => MyBilinear u v



end MySpacetime
