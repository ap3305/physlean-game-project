import GameServer
import Game.Metadata
import Game.Theorems.Space.Theorems

open MySpace

namespace my_inner

opaque my_inner : MySpace -> MySpace -> ℝ

notation "≪" u ", " v "≫" => my_inner u v

axiom inner_comm (u v : MySpace) : ≪u, v≫ = ≪v, u≫
axiom inner_add (u v w : MySpace) : ≪u, v + w≫ = ≪u, v≫ + ≪u, w≫
axiom inner_smul (u v : MySpace) (a : ℝ) : ≪u, a • v≫ = a * ≪u, v≫



lemma add_inner (u v w : MySpace) : ≪u + v, w≫ = ≪u, w≫ + ≪v, w≫ := by
  simp only [inner_comm, inner_add]

lemma smul_inner (u v : MySpace) (a : ℝ) : ≪a • u, v≫ = a * ≪u, v≫ := by
  simp only [inner_comm, inner_smul]

lemma inner_zero (v : MySpace) : ≪v, 0≫ = 0 := by
  have h : ≪v, 0≫ = ≪v, 0≫ + ≪v, 0≫ := by
    nth_rewrite 1 [← vector_add_zero (0 : MySpace)]
    rw [inner_add]
  simp at h
  assumption

lemma inner_self_add (u v : MySpace) : ≪u + v, u + v≫ = ≪u, u≫ + 2 * ≪u, v≫ + ≪v, v≫ := by
  simp only [inner_comm, inner_add]
  ring

macro "inner_simp_" : tactic => `(tactic| simp only [
  inner_comm, inner_add, inner_smul, inner_zero
])

end my_inner
