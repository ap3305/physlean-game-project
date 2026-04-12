import GameServer
import Game.Metadata

@[ext]
structure MySpace where
  x : ℝ
  y : ℝ
  z : ℝ

-- { x := , y := , z :=  }

namespace MySpace

instance : Add MySpace where
  add u v := { x := u.x + v.x, y := u.y + v.y, z := u.z + v.z }

instance : Sub MySpace where
  sub u v := { x := u.x - v.x, y := u.y - v.y, z := u.z - v.z }

instance : Neg MySpace where
  neg u := { x := -u.x, y := -u.y, z := -u.z }

instance : SMul ℝ MySpace where
  smul a u := { x := a * u.x, y := a * u.y, z := a * u.z }

instance : Zero MySpace where
  zero := { x := 0, y := 0, z := 0 }


@[simp] lemma add_x (u v : MySpace) : (u + v).x = u.x + v.x := rfl
@[simp] lemma add_y (u v : MySpace) : (u + v).y = u.y + v.y := rfl
@[simp] lemma add_z (u v : MySpace) : (u + v).z = u.z + v.z := rfl

@[simp] lemma zero_x : (0 : MySpace).x = 0 := rfl
@[simp] lemma zero_y : (0 : MySpace).y = 0 := rfl
@[simp] lemma zero_z : (0 : MySpace).z = 0 := rfl

@[simp] lemma neg_x (u : MySpace) : (-u).x = -u.x := rfl
@[simp] lemma neg_y (u : MySpace) : (-u).y = -u.y := rfl
@[simp] lemma neg_z (u : MySpace) : (-u).z = -u.z := rfl

@[simp] lemma smul_x (u : MySpace) (a : ℝ) : (a • u).x = a * u.x := rfl
@[simp] lemma smul_y (u : MySpace) (a : ℝ) : (a • u).y = a * u.y := rfl
@[simp] lemma smul_z (u : MySpace) (a : ℝ) : (a • u).z = a * u.z := rfl


lemma vector_add_zero (u : MySpace) : u + (0 : MySpace) = u := by
  ext
  all_goals simp

lemma vector_add_inv (u : MySpace) : u + (-u) = 0 := by
  ext
  all_goals simp

lemma vector_add_comm (u v : MySpace) : u + v = v + u := by
  ext
  all_goals
    simp
    ring

lemma vector_add_assoc (u v w : MySpace) : u + (v + w) = (u + v) + w := by
  ext
  all_goals
    simp
    ring

lemma vector_smul_one (u : MySpace) : (1 : ℝ) • u = u := by
  ext
  all_goals
    simp

lemma vector_smul_add (u v : MySpace) (a : ℝ) : a • (u + v) = a • u + a • v := by
  ext
  all_goals
    simp
    ring

lemma vector_add_smul (u : MySpace) (a b : ℝ) : (a + b) • u = a • u + b • u := by
  ext
  all_goals
    simp
    ring

lemma vector_smul_assoc (u : MySpace) (a b : ℝ) : a • (b • u) = (a * b) • u := by
  ext
  all_goals
    simp
    ring

macro "simp_vector" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [
  vector_add_zero, vector_add_inv, vector_add_comm, vector_add_assoc,
  vector_smul_one, vector_smul_add, ← vector_add_smul, vector_smul_assoc,
] $(loc)? <;> ring <;> simp only [vector_add_comm]
)

end MySpace
