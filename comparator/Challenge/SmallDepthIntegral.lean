module

public import Challenge.SmallDepthFlux

@[expose] public section

/- Frozen input: Liu/SmallDepthIntegral.lean -/
noncomputable section
open Set Real MeasureTheory
namespace Liu

theorem small_depth_flux_integral {s γ u v : ℝ} (hg : γ∈Icc 0 (π/2)) (hu : 0<u)
    (huv : u≤v) (hv : v≤1/4) :
    (∫ t in u..v, |flux s γ t|)≤(2^34/(Certificate.smallMass s)^2)*v*(2+log (1/v)) := by sorry

end Liu
end
