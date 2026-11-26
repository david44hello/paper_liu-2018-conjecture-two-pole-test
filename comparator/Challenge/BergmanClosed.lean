import Challenge.QuotientDomain
import Challenge.PickSums
import Challenge.RadialEnergy
import Mathlib.Analysis.Complex.MeanValue

/- Frozen input: Liu/BergmanClosed.lean -/
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
namespace Liu

theorem analyticVectors_closed : IsClosed analyticVectors := by sorry

theorem bergman_projection_range : analyticSubspace = representativeSubspace := by sorry

end Liu
end
