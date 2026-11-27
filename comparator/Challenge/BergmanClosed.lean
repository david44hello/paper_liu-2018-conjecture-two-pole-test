module

public import Challenge.QuotientDomain
public import Challenge.PickSums
public import Challenge.RadialEnergy
public import Mathlib.Analysis.Complex.MeanValue

@[expose] public section

/- Frozen input: Liu/BergmanClosed.lean -/
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
namespace Liu

theorem analyticVectors_closed : IsClosed analyticVectors := by sorry

theorem bergman_projection_range : analyticSubspace = representativeSubspace := by sorry

end Liu
end
