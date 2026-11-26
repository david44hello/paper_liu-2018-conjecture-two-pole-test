import Challenge.SupercriticalEnergy
import Challenge.ProjectionKernel
import Challenge.QuotientDomain
import Challenge.PickSums
import Challenge.RadialEnergy
import Challenge.FieldBound
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Challenge.BoundaryField
import Challenge.LogSource
import Challenge.Pick
import Challenge.Projection

/- Frozen input: Liu/FieldComparison.lean -/
noncomputable section
open Set MeasureTheory Filter Real
open scoped ComplexConjugate Topology
namespace Liu

theorem canonicalField_uniform_cubic_error {K : ℝ} (hK : 0≤K) :
    ∃ C ≥ 0, ∀ (f : ℂ → ℂ), Measurable f →
      (∀ w∈upper, ‖f w‖≤K/(1+‖w‖)^3) →
      ∀ z : ℂ, 0≤z.im → 1<‖z‖ → ‖canonicalField f z‖≤C*(1+log ‖z‖)/‖z‖^2 := by sorry

end Liu
end
