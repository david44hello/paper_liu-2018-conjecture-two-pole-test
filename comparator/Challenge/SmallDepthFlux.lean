import Challenge.EdgeTraceEstimates
import Challenge.PoissonLine
import Challenge.SingleFlux
import Challenge.DepthDerivative

/- Frozen input: Liu/SmallDepthFlux.lean -/
noncomputable section
open Set Real MeasureTheory Filter
open scoped Topology
namespace Liu

theorem small_depth_flux_estimate : Certificate.smallDepthEstimate := by sorry

end Liu
end
