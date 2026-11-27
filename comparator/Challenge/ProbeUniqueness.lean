module

public import Challenge.IntegrableReproducing
public import Challenge.FinitePart
public import Challenge.Pick
public import Challenge.PickSums
public import Challenge.Projection
public import Challenge.Reproducing
public import Challenge.LogSource

@[expose] public section

/- Frozen input: Liu/ProbeUniqueness.lean -/
noncomputable section
open Set MeasureTheory Real Metric
open scoped ComplexConjugate
namespace Liu

theorem halfPlane_probe_uniqueness {V : ℂ → ℂ} (hd : DifferentiableOn ℂ V upper)
    (hc : ContinuousOn V {w : ℂ | 0≤w.im}) {T K : ℝ} (hK : 0≤K)
    (hfar : ∀ w ∈ upper, T ≤ ‖w‖ → ‖V w‖ ≤ K*(1+log ‖w‖)/‖w‖)
    (hm : ∀ m : ℕ, ∫ w, V w*conj (uniquenessProbe m w) ∂upperArea = 0) :
    ∀ z ∈ upper, V z=0 := by sorry

end Liu
end
