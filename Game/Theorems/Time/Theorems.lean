import GameServer
import Game.Metadata

@[ext]
structure MyTime where
  val : ℝ

def is_past (t: MyTime) : Prop := t.val < 0

def is_present (t: MyTime) : Prop := t.val == 0

def is_future (t: MyTime) : Prop := t.val > 0
