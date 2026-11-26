import Challenge.EdgeTraceEstimates
import Challenge.PoissonLine
import Challenge.SingleFlux
import Challenge.SmallDepthIntegral

/- Frozen input: Liu/MixedEdgeFlux.lean -/
noncomputable section
open Set Real MeasureTheory Filter
open scoped Topology
namespace Liu

theorem mixed_edge_flux_estimate : Certificate.mixedEdgeEstimate := by sorry

end Liu
end
