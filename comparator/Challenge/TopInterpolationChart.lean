module

public import Challenge.InterpolationCharts

@[expose] public section

/- Frozen input: Liu/TopInterpolationChart.lean -/
noncomputable section
open Real Set
open scoped Topology ComplexConjugate
namespace Liu

def topCellFlux (L : CellLine) (r : ℝ) : ℝ :=
  let v := reciprocalScale*(1-(L.y₀+L.y₁*r))
  reciprocalScale * v⁻¹ * boundaryFlux (unitDepthSum (L.s₀+L.s₁*r) (L.realAngle r) v)

end Liu
end
