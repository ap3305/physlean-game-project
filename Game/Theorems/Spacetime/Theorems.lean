import GameServer
import Game.Metadata
import Game.Theorems.Space.Theorems
import Game.Theorems.Time.Theorems

@[ext]
structure MySpacetime where
  time : MyTime
  space : MySpace

namespace MySpacetime

instance : Add MySpacetime where
  add u v := { time := u.time + v.time, space := u.space + v.space }

instance : Sub MySpacetime where
  sub u v := { time := u.time - v.time, space := u.space - v.space }

instance : Neg MySpacetime where
  neg u := { time := -u.time, space := -u.space }

instance : SMul ℝ MySpacetime where
  smul a u := { time := a • u.time, space := a • u.space }

instance : Zero MySpacetime where
  zero := { time := 0, space := 0 }

@[simp] lemma add_time (u v : MySpacetime) : (u + v).time = u.time + v.time := rfl
@[simp] lemma add_space (u v : MySpacetime) : (u + v).space = u.space + v.space := rfl

@[simp] lemma zero_time : (0 : MySpacetime).time = 0 := rfl
@[simp] lemma zero_space : (0 : MySpacetime).space = 0 := rfl

@[simp] lemma neg_time (u : MySpacetime) : (-u).time = -u.time := rfl
@[simp] lemma neg_space (u : MySpacetime) : (-u).space = -u.space := rfl

@[simp] lemma smul_time (u : MySpacetime) (a : ℝ) : (a • u).time = a • u.time := rfl
@[simp] lemma smul_space (u : MySpacetime) (a : ℝ) : (a • u).space = a • u.space := rfl

abbrev x (u : MySpacetime) : ℝ := u.space.x
abbrev y (u : MySpacetime) : ℝ := u.space.y
abbrev z (u : MySpacetime) : ℝ := u.space.z
abbrev t (u : MySpacetime) : ℝ := u.time.val

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

def MyBilinear (u v : MySpacetime) : ℝ := u.t * v.t - u.x * v.x - u.y * v.y - u.z * v.z

notation "≪" u ", " v "≫" => MyBilinear u v



end MySpacetime
