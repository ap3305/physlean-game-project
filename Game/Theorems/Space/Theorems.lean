import GameServer
import Game.Metadata

@[ext]
structure Space where
  x : ℝ
  y : ℝ
  z : ℝ

-- { x := , y := , z :=  }

instance : Add Space where
  add u v := { x := u.x + v.x, y := u.y + v.y, z := u.z + v.z }

instance : Sub Space where
  sub u v := { x := u.x - v.x, y := u.y - v.y, z := u.z - v.z }

instance : Neg Space where
  neg u := { x := -u.x, y := -u.y, z := -u.z }

instance : SMul ℝ Space where
  smul a u := { x := a * u.x, y := a * u.y, z := a * u.z }

instance : Zero Space where
  zero := { x := 0, y := 0, z := 0 }

@[simp]
def dot_product (u v : Space) := u.x * v.x + u.y * v.y + u.z * v.z

infix:100 " • " => dot_product

@[simp] lemma add_x (u v : Space) : (u + v).x = u.x + v.x := rfl
@[simp] lemma add_y (u v : Space) : (u + v).y = u.y + v.y := rfl
@[simp] lemma add_z (u v : Space) : (u + v).z = u.z + v.z := rfl

@[simp] lemma zero_x : (0 : Space).x = 0 := rfl
@[simp] lemma zero_y : (0 : Space).y = 0 := rfl
@[simp] lemma zero_z : (0 : Space).z = 0 := rfl

@[simp] lemma neg_x (u : Space) : (-u).x = -u.x := rfl
@[simp] lemma neg_y (u : Space) : (-u).y = -u.y := rfl
@[simp] lemma neg_z (u : Space) : (-u).z = -u.z := rfl

@[simp] lemma smul_x (u : Space) (a : ℝ) : (a • u).x = a * u.x := rfl
@[simp] lemma smul_y (u : Space) (a : ℝ) : (a • u).y = a * u.y := rfl
@[simp] lemma smul_z (u : Space) (a : ℝ) : (a • u).z = a * u.z := rfl

@[simp]
lemma vector_add_zero (u : Space) : u + (0 : Space) = u := by
  ext
  all_goals simp

@[simp]
lemma vector_add_inv (u : Space) : u + (-u) = 0 := by
  ext
  all_goals simp

@[simp]
lemma vector_add_comm (u v : Space) : u + v = v + u := by
  ext
  all_goals
    simp
    ring

@[simp]
lemma vector_add_assoc (u v w : Space) : u + (v + w) = (u + v) + w := by
  ext
  all_goals
    simp
    ring

@[simp]
lemma vector_smul_one (u : Space) : (1 : ℝ) • u = u := by
  ext
  all_goals
    simp

@[simp]
lemma vector_smul_add (u v : Space) (a : ℝ) : a • (u + v) = a • u + a • v := by
  ext
  all_goals
    simp
    ring

@[simp]
lemma vector_add_smul (u : Space) (a b : ℝ) : (a + b) • u = a • u + b • u := by
  ext
  all_goals
    simp
    ring

@[simp]
lemma vector_smul_assoc (u : Space) (a b : ℝ) : a • (b • u) = (a * b) • u := by
  ext
  all_goals
    simp
    ring
