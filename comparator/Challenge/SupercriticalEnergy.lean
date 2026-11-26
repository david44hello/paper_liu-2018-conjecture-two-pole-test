import Challenge.CanonicalRegularity
import Challenge.CanonicalField
import Challenge.FinitePart
import Challenge.Pick
import Challenge.PickSums
import Challenge.Projection
import Challenge.Reproducing
import Challenge.LogSource
import Challenge.FarFieldClaim
import Mathlib.Analysis.Complex.CauchyIntegral

/- Frozen input: Liu/SupercriticalEnergy.lean -/
noncomputable section
open Set MeasureTheory Real Filter Metric
open scoped Topology ComplexConjugate
namespace Liu

structure SupercriticalSource (f : ℂ → ℂ) (t : ℝ) : Prop where
  pos : 0 < t
  lt_one : t < 1
  measurable : Measurable f
  bound : ∃ K ≥ 0, ∀ w ∈ upper, ‖f w‖ ≤ K/(1+‖w‖)^(2+t)

end Liu
end
