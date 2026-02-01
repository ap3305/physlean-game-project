import GameServer
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Basic
-- import PhysLean.SpaceAndTime.Space.Basic

@[ext]

structure Space where
  x : ℝ
  y : ℝ
  z : ℝ

-- { x := , y := , z :=  }

instance : Add Space where
  add u v := { x := u.x + v.x, y := u.y + v.y, z := u.z + v.z }

instance : SMul ℝ Space where
  smul a u := { x := a * u.x, y := a * u.y, z := a * u.z }

instance : Zero Space where
  zero := { x := 0, y := 0, z := 0 }

def dot_product (u v : Space) := u.x * v.x + u.y * v.y + u.z * v.z

infix:100 " • " => dot_product

lemma add_x (u v : Space) : (u + v).x = u.x + v.x := rfl
lemma add_y (u v : Space) : (u + v).y = u.y + v.y := rfl
lemma add_z (u v : Space) : (u + v).z = u.z + v.z := rfl

lemma zero_x : (0 : Space).x = 0 := rfl
lemma zero_y : (0 : Space).y = 0 := rfl
lemma zero_z : (0 : Space).z = 0 := rfl

lemma vector_add_zero (u : Space) : u + (0 : Space) = u := by
  ext
  rw [add_x]
  rw [zero_x]
  rw [add_zero]
  rw [add_y]
  rw [zero_y]
  rw [add_zero]
  rw [add_z]
  rw [zero_z]
  rw [add_zero]

lemma vector_comm (u v : Space) : u + v = v + u := by
  ext
  repeat rw [add_x]
  rw [add_comm]
  repeat rw [add_y]
  rw [add_comm]
  repeat rw [add_z]
  rw [add_comm]
