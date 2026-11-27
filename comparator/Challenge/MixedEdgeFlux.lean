module

public import Challenge.EdgeTraceEstimates
public import Challenge.PoissonLine
public import Challenge.SingleFlux
public import Challenge.SmallDepthIntegral

@[expose] public section

/- Frozen input: Liu/MixedEdgeFlux.lean -/
noncomputable section
open Set Real MeasureTheory Filter
open scoped Topology
namespace Liu

theorem mixed_edge_flux_estimate : Certificate.mixedEdgeEstimate := by sorry

end Liu
end
