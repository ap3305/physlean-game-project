import GameServer
import Mathlib.Data.Fin.VecNotation
import PhysLean.SpaceAndTime.space.Basic

abbrev space : Type := Space

namespace space

@[simp] def x (v : space) : ℝ := v 0
@[simp] def y (v : space) : ℝ := v 1
@[simp] def z (v : space) : ℝ := v 2

@[ext]
lemma space_ext (u v : space) (hx : u.x = v.x) (hy : u.y = v.y) (hz : u.z = v.z) : u = v := by
  funext i
  fin_cases i
  exact hx
  exact hy
  exact hz

end space

@[simp]
lemma x_val (a : ℝ) (t : Fin 2 → ℝ) : space.x (Matrix.vecCons a t : space) = a := by
  simp
@[simp]
lemma y_val (a b : ℝ) (t : Fin 1 → ℝ) : space.y (Matrix.vecCons a (Matrix.vecCons b t)) = b := by
  simp
@[simp]
lemma z_val (a b c : ℝ) : space.z (Matrix.vecCons a (Matrix.vecCons b (Matrix.vecCons c Matrix.vecEmpty))) = c := by
  simp


lemma vector_add_zero (u : space) : u + 0 = u := by
  simp

lemma vector_comm (u v : space) : u + v = v + u := by
  ext
  all_goals
    simp
    ring
