import Challenge.FinitePart
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/- Frozen input: Liu/RadialEnergy.lean -/
noncomputable section
open Set MeasureTheory Real
namespace Liu

def radialTail (q : ℝ) (z : ℂ) : ℝ :=
  if 1 < ‖z‖ then ‖z‖^(-q) else 0

end Liu
end
