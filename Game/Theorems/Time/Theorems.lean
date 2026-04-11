import GameServer
import Game.Metadata

@[ext]
structure MyTime where
  val : ℝ

namespace MyTime

instance : Add MyTime where
  add u v := { val := u.val + v.val }

instance : Sub MyTime where
  sub u v := { val := u.val - v.val }

instance : Neg MyTime where
  neg u := { val := -u.val }

instance : SMul ℝ MyTime where
  smul a u := { val := a * u.val }

instance : Zero MyTime where
  zero := { val := 0 }

@[simp] lemma add_val (u v : MyTime) : (u + v).val = u.val + v.val := rfl

@[simp] lemma zero_val : (0 : MyTime).val = 0 := rfl

@[simp] lemma neg_val (u : MyTime) : (-u).val = -u.val := rfl

@[simp] lemma smul_val (u : MyTime) (a : ℝ) : (a • u).val = a * u.val := rfl

inductive TimeCharacter
  | past
  | present
  | future
deriving DecidableEq

noncomputable def timeCharacter (t : MyTime) : TimeCharacter :=
  if t.val = 0 then TimeCharacter.present
  else if 0 < t.val then TimeCharacter.future
  else TimeCharacter.past

end MyTime
