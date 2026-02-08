import GameServer
import Game.Metadata

@[ext]
structure MySpacetime where
  t : ℝ
  x : ℝ
  y : ℝ
  z : ℝ

namespace MySpacetime

instance : Add MySpacetime where
  add u v := { t := u.t + v.t, x := u.x + v.x, y := u.y + v.y, z := u.z + v.z }

instance : Sub MySpacetime where
  sub u v := { t := u.t - v.t, x := u.x - v.x, y := u.y - v.y, z := u.z - v.z }

instance : Neg MySpacetime where
  neg u := { t := -u.t, x := -u.x, y := -u.y, z := -u.z }

instance : SMul ℝ MySpacetime where
  smul a u := { t := a * u.t, x := a * u.x, y := a * u.y, z := a * u.z }

instance : Zero MySpacetime where
  zero := { t := 0, x := 0, y := 0, z := 0 }

@[simp] lemma add_t (u v : MySpacetime) : (u + v).t = u.t + v.t := rfl
@[simp] lemma add_x (u v : MySpacetime) : (u + v).x = u.x + v.x := rfl
@[simp] lemma add_y (u v : MySpacetime) : (u + v).y = u.y + v.y := rfl
@[simp] lemma add_z (u v : MySpacetime) : (u + v).z = u.z + v.z := rfl

@[simp] lemma zero_t : (0 : MySpacetime).t = 0 := rfl
@[simp] lemma zero_x : (0 : MySpacetime).x = 0 := rfl
@[simp] lemma zero_y : (0 : MySpacetime).y = 0 := rfl
@[simp] lemma zero_z : (0 : MySpacetime).z = 0 := rfl

@[simp] lemma neg_t (u : MySpacetime) : (-u).t = -u.t := rfl
@[simp] lemma neg_x (u : MySpacetime) : (-u).x = -u.x := rfl
@[simp] lemma neg_y (u : MySpacetime) : (-u).y = -u.y := rfl
@[simp] lemma neg_z (u : MySpacetime) : (-u).z = -u.z := rfl

@[simp] lemma smul_t (u : MySpacetime) (a : ℝ) : (a • u).t = a * u.t := rfl
@[simp] lemma smul_x (u : MySpacetime) (a : ℝ) : (a • u).x = a * u.x := rfl
@[simp] lemma smul_y (u : MySpacetime) (a : ℝ) : (a • u).y = a * u.y := rfl
@[simp] lemma smul_z (u : MySpacetime) (a : ℝ) : (a • u).z = a * u.z := rfl


def my_minkowski : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![1, -1, -1, -1]

notation "η" => my_minkowski

def my_inner (u v : MySpacetime) : ℝ := u.t * v.t - u.x * v.x - u.y * v.y - u.z * v.z

notation "≪" u ", " v "≫" => my_inner u v



end MySpacetime
