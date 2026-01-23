import GameServer
import PhysLean.Units.Dimension
import PhysLean.Units.UnitDependent

def LengthDim : Dimension := ⟨1, 0, 0, 0, 0⟩
def TimeDim : Dimension := ⟨0, 1, 0, 0, 0⟩
def MassDim : Dimension := ⟨0, 0, 1, 0, 0⟩
def ChargeDim : Dimension := ⟨0, 0, 0, 1, 0⟩
def TemperatureDim : Dimension := ⟨0, 0, 0, 0, 1⟩

def AreaDim : Dimension := ⟨2, 0, 0, 0, 0⟩
def VelocityDim : Dimension := ⟨1, -1, 0, 0, 0⟩
def EnergyDim : Dimension := ⟨2, -2, 1, 0, 0⟩
