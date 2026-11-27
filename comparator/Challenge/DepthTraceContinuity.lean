module

public import Challenge.EdgeTrace

@[expose] public section

/- Frozen input: Liu/DepthTraceContinuity.lean -/
noncomputable section
open Set Real MeasureTheory Filter Metric
open scoped ComplexConjugate Topology
namespace Liu

def depthTranslate (S : ℂ → ℂ) (t : ℝ) (z : ℂ) := S (z+(t:ℂ)*Complex.I)

end Liu
end
