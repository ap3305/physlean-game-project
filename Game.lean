import Game.Levels.Space
import Game.Levels.Time
import Game.Levels.Bilinear
import Game.Levels.Spacetime

-- Here's what we'll put on the title screen
Title "PhysLean Game"
Introduction
"
## Welcome to [Game time]
In this game we will work up from vectors to properties of points in spacetime, branching at at points along the way.

The contents of this game follow the structure of PhysLean, a physics based Lean library which aims to be the physics counterpart of Mathlib, providing easy access to previous work and a platform to build off of, in this game you will prove some of the existing results PhysLean provides in order to hopefully create a point for you to leap off from into the PhysLean documentation to find any result you may need.

To find out more about PhysLean, you can visit https://physlean.com/.
"

Info "
Here you can put additional information about the game. It is accessible
from the starting through the drop-down menu.

For example: Game version, Credits, Link to Github and Zulip, etc.

Use **markdown**.
"

/-! Information to be displayed on the servers landing page. -/
Languages "en"
CaptionShort "Game Template"
CaptionLong "You should use this game as a template for your own game and add your own levels."
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"
Dependency Space → Time → Spacetime
Dependency Space → Bilinear → Spacetime

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
