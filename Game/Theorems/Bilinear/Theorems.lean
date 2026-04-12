import GameServer
import Game.Metadata
import Game.Theorems.Space.Theorems

open MySpace

namespace MyBilinear

opaque MyBilinear : MySpace -> MySpace -> ℝ

notation "≪" u ", " v "≫" => MyBilinear u v

axiom bilinear_comm (u v : MySpace) : ≪u, v≫ = ≪v, u≫
axiom bilinear_add (u v w : MySpace) : ≪u, v + w≫ = ≪u, v≫ + ≪u, w≫
axiom bilinear_smul (u v : MySpace) (a : ℝ) : ≪u, a • v≫ = a * ≪u, v≫



lemma add_bilinear (u v w : MySpace) : ≪u + v, w≫ = ≪u, w≫ + ≪v, w≫ := by
  simp only [bilinear_comm, bilinear_add]

lemma smul_bilinear (u v : MySpace) (a : ℝ) : ≪a • u, v≫ = a * ≪u, v≫ := by
  simp only [bilinear_comm, bilinear_smul]

lemma bilinear_zero (v : MySpace) : ≪v, 0≫ = 0 := by
  have h : ≪v, 0≫ = ≪v, 0≫ + ≪v, 0≫ := by
    nth_rewrite 1 [← vector_add_zero (0 : MySpace)]
    rw [bilinear_add]
  simp at h
  assumption

lemma bilinear_neg (u v : MySpace) : ≪u, -v≫ = -≪u, v≫ := by
  have h : -v = (-1 : ℝ) • v := by
    ext <;> simp
  rw [h]
  rw [bilinear_smul]
  norm_num

lemma bilinear_self_add (u v : MySpace) : ≪u + v, u + v≫ = ≪u, u≫ + 2 * ≪u, v≫ + ≪v, v≫ := by
  simp only [bilinear_comm, bilinear_add]
  ring


macro "simp_bilinear" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [
  bilinear_comm, bilinear_add, bilinear_smul, bilinear_zero, bilinear_neg
] $(loc)?)

end MyBilinear
