module

public import Challenge.EdgeTraceEstimates
public import Challenge.PoissonLine
public import Challenge.SingleFlux
public import Challenge.DepthDerivative

@[expose] public section

/- Frozen input: Liu/SmallDepthFlux.lean -/
noncomputable section
open Set Real MeasureTheory Filter
open scoped Topology
namespace Liu

theorem small_depth_flux_estimate : Certificate.smallDepthEstimate := by sorry

end Liu
end
