module

public import Challenge.FinitePart
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

/- Frozen input: Liu/RadialEnergy.lean -/
noncomputable section
open Set MeasureTheory Real
namespace Liu

def radialTail (q : ℝ) (z : ℂ) : ℝ :=
  if 1 < ‖z‖ then ‖z‖^(-q) else 0

end Liu
end
