module

public import Challenge.CanonicalRegularity
public import Challenge.CanonicalField
public import Challenge.FinitePart
public import Challenge.Pick
public import Challenge.PickSums
public import Challenge.Projection
public import Challenge.Reproducing
public import Challenge.LogSource
public import Challenge.FarFieldClaim
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section

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
