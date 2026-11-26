import Challenge.IntegrableReproducing
import Challenge.FinitePart
import Challenge.Pick
import Challenge.PickSums
import Challenge.Projection
import Challenge.Reproducing
import Challenge.LogSource

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
