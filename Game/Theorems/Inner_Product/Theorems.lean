import GameServer
import Game.Metadata
import Game.Theorems.Space.Theorems

opaque my_inner : MySpace -> MySpace -> ℝ

notation "≪" u ", " v "≫" => my_inner u v

axiom inner_comm (u v : MySpace) : ≪u, v≫ = ≪v, u≫
axiom inner_add (u v w : MySpace) : ≪u + v, w≫ = ≪u, w≫ + ≪v, w≫
axiom inner_smul (u v : MySpace) (a : ℝ) : ≪a • u, v≫ = a * ≪u, v≫

lemma add_inner (u v w : MySpace) : ≪u, v + w≫ = ≪u, v≫ + ≪u, w≫ := by
  rw [inner_comm]
  rw [inner_add]
  rw [inner_comm]
  nth_rewrite 2 [inner_comm]
  rfl
