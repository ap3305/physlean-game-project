import Game.Levels.Space
import Game.Levels.Time
import Game.Levels.Bilinear
import Game.Levels.Spacetime


Title "PhysLean Game"
Introduction
"
## Welcome to PhysLean!
In this game we will work up from vectors to spacetime, branching at points along the way.

The contents of this game follow the structure of PhysLean, a physics based Lean library which aims to be the physics counterpart of Mathlib, providing easy access to previous work and a platform to build off of, in this game you will prove some of the existing results PhysLean provides in order to hopefully create a point for you to leap off from into the PhysLean documentation to find any result you may need.

To find out more about PhysLean, you can visit https://physlean.com/.
"

Info "
Game version - 1.0.0
Credits:
  - Joseph Tooby-Smith - Founding PhysLean and supervising this project.
  - Alexander Pettett - Creating the game.
"

/-! Information to be displayed on the servers landing page. -/
Languages "en"
CaptionShort "PhysLean Game"
CaptionLong "This game aims to serve as an entry point into physics formalistation through the lens of PhysLean, the biggest library for physics in Lean."
Prerequisites "Natural Numbers Game"

Dependency Space → Time
Dependency Space → Bilinear
Dependency Time → Spacetime
Dependency Bilinear → Spacetime

MakeGame
