import Challenge.FarDeficit
import Challenge.DepthTraceContinuity

/- Frozen input: Liu/DepthFluxContinuity.lean -/
noncomputable section
open Set Real Filter MeasureTheory Metric
open scoped Topology
namespace Liu

def boundaryFlux (S : ℂ → ℂ) :=
  (∫ x : ℝ, ‖field S x‖^2-k₀*‖S x‖^2)/π

end Liu
end
