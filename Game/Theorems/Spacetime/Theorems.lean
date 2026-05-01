import GameServer
import Game.Metadata
import Game.Theorems.Space.Theorems
import Game.Theorems.Time.Theorems
import Game.Theorems.Bilinear.Theorems

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

@[simp] abbrev x (u : MySpacetime) : ℝ := u.space.x
@[simp] abbrev y (u : MySpacetime) : ℝ := u.space.y
@[simp] abbrev z (u : MySpacetime) : ℝ := u.space.z
@[simp] abbrev t (u : MySpacetime) : ℝ := u.time.val

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


lemma vector_add_zero (u : MySpacetime) : u + (0 : MySpacetime) = u := by
  ext
  all_goals simp

lemma vector_add_inv (u : MySpacetime) : u + (-u) = 0 := by
  ext
  all_goals simp

lemma vector_add_comm (u v : MySpacetime) : u + v = v + u := by
  ext
  all_goals
    simp
    ring

lemma vector_add_assoc (u v w : MySpacetime) : u + (v + w) = (u + v) + w := by
  ext
  all_goals
    simp
    ring

lemma vector_smul_one (u : MySpacetime) : (1 : ℝ) • u = u := by
  ext
  all_goals
    simp

lemma vector_smul_add (u v : MySpacetime) (a : ℝ) : a • (u + v) = a • u + a • v := by
  ext
  all_goals
    simp
    ring

lemma vector_add_smul (u : MySpacetime) (a b : ℝ) : (a + b) • u = a • u + b • u := by
  ext
  all_goals
    simp
    ring

lemma vector_smul_assoc (u : MySpacetime) (a b : ℝ) : a • (b • u) = (a * b) • u := by
  ext
  all_goals
    simp
    ring

macro "vector_simp" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [
  vector_add_zero, vector_add_inv, vector_add_comm, vector_add_assoc,
  vector_smul_one, vector_smul_add, ← vector_add_smul, vector_smul_assoc,
] $(loc)? <;> ring <;> simp only [vector_add_comm]
)


def my_minkowski : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![1, -1, -1, -1]

notation "η" => my_minkowski

@[simp]
def MyBilinear (u v : MySpacetime) : ℝ := u.t * v.t - u.x * v.x - u.y * v.y - u.z * v.z

notation "≪" u ", " v "≫" => MyBilinear u v


lemma bilinear_comm (u v : MySpacetime) : ≪u, v≫ = ≪v, u≫ := by
  simp
  ring

lemma bilinear_add (u v w : MySpacetime) : ≪u, v + w≫ = ≪u, v≫ + ≪u, w≫ := by
  simp
  ring

lemma bilinear_smul (u v : MySpacetime) (a : ℝ) : ≪u, a • v≫ = a * ≪u, v≫ := by
  simp
  ring

lemma add_bilinear (u v w : MySpacetime) : ≪u + v, w≫ = ≪u, w≫ + ≪v, w≫ := by
  simp only [bilinear_comm, bilinear_add]

lemma smul_bilinear (u v : MySpacetime) (a : ℝ) : ≪a • u, v≫ = a * ≪u, v≫ := by
  simp only [bilinear_comm, bilinear_smul]

lemma bilinear_zero (v : MySpacetime) : ≪v, 0≫ = 0 := by
  have h : ≪v, 0≫ = ≪v, 0≫ + ≪v, 0≫ := by
    nth_rewrite 1 [← vector_add_zero (0 : MySpacetime)]
    rw [bilinear_add]
  simp

lemma bilinear_neg (u v : MySpacetime) : ≪u, -v≫ = -≪u, v≫ := by
  have h : -v = (-1 : ℝ) • v := by
    ext <;> simp
  rw [h]
  rw [bilinear_smul]
  norm_num

lemma bilinear_self_add (u v : MySpacetime) : ≪u + v, u + v≫ = ≪u, u≫ + 2 * ≪u, v≫ + ≪v, v≫ := by
  simp only [bilinear_comm, bilinear_add]
  ring


macro "simp_bilinear" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [
  bilinear_comm, bilinear_add, bilinear_smul, bilinear_zero, bilinear_neg
] $(loc)?)



-- https://github.com/leanprover-community/physlib/blob/9ca1ee1d0cac43391399fcdc9e9fca8c94c17057/Physlib/Relativity/Tensors/RealTensor/Vector/Causality/Basic.lean#L25-L31
inductive CausalCharacter
  | timeLike
  | lightLike
  | spaceLike
deriving DecidableEq

noncomputable def causalCharacter (p : MySpacetime) : CausalCharacter :=
  let v0 := ≪p, p≫
  if v0 = 0 then CausalCharacter.lightLike
  else if 0 < v0 then CausalCharacter.timeLike
  else CausalCharacter.spaceLike

end MySpacetime
