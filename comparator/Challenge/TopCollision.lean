module

public import Challenge.SeparatedSource
public import Challenge.TopInterpolationChart

@[expose] public section

/- Frozen input: Liu/TopCollision.lean -/
noncomputable section
open Set Real MeasureTheory Filter
open scoped Topology
namespace Liu

theorem top_focus_limit (s γ : ℝ) :
    Tendsto (fun v : ℝ => v⁻¹ * boundaryFlux (unitDepthSum s γ v)) (𝓝 0) (𝓝 0) := by sorry

end Liu
end
