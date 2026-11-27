module

public import Challenge.SlopeFormula
public import Challenge.BoundaryField
public import Challenge.PoissonLine

@[expose] public section

/- Frozen input: Liu/SinglePoleReduction.lean -/
noncomputable section
open Set MeasureTheory Filter Real
open scoped Topology
namespace Liu

def capPower (u : ℝ) (z : ℂ) := (z+Complex.I)^(-(u:ℂ))

end Liu
end
