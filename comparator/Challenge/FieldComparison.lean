module

public import Challenge.SupercriticalEnergy
public import Challenge.ProjectionKernel
public import Challenge.QuotientDomain
public import Challenge.PickSums
public import Challenge.RadialEnergy
public import Challenge.FieldBound
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Challenge.BoundaryField
public import Challenge.LogSource
public import Challenge.Pick
public import Challenge.Projection

@[expose] public section

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
