import Challenge.SlopeFormula
import Challenge.BoundaryField
import Challenge.PoissonLine

/- Frozen input: Liu/SinglePoleReduction.lean -/
noncomputable section
open Set MeasureTheory Filter Real
open scoped Topology
namespace Liu

def capPower (u : ℝ) (z : ℂ) := (z+Complex.I)^(-(u:ℂ))

end Liu
end
