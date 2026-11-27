module

public import Challenge.AngularDeficit
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.LocalExtr.Rolle
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Challenge.AngularPotential
public import Challenge.LogSource
public import Challenge.SupercriticalEnergy
public import Challenge.ProjectionKernel
public import Challenge.QuotientDomain
public import Challenge.PickSums
public import Challenge.RadialEnergy
public import Challenge.FinitePart
public import Challenge.Pick
public import Challenge.Projection
public import Challenge.Reproducing
public import Challenge.FarFieldClaim
public import Challenge.CanonicalField
public import Challenge.Orthogonality
public import Challenge.FieldComparison
public import Challenge.WitnessClaim
public import Challenge.FinitePartLaws

@[expose] public section

/- Frozen input: Liu/SlopeFormula.lean -/
noncomputable section
open Set MeasureTheory Filter Real Metric
open scoped Topology
namespace Liu

theorem PickSum.slope_formula {n : ℕ} (p : PickSum n) :
    Tendsto (fun t : ℝ => (quotient (p.power (1+t))-k₀)/t) (𝓝[>] 0)
      (𝓝 (2*(k₀-deficit p.value/p.mass^2))) ∧
    2*(k₀-deficit p.value/p.mass^2) = -2*(deficit p.value/p.mass^2-k₀) := by sorry

theorem PickSum.slope_remainder {n : ℕ} (p : PickSum n) :
    Tendsto (fun t : ℝ => (quotient (p.power (1+t))-k₀-
      (2*(k₀-deficit p.value/p.mass^2))*t)/t) (𝓝[>] 0) (𝓝 0) := by sorry

theorem PickSum.quotient_side_of_margin {n : ℕ} (p : PickSum n) :
    (0<deficit p.value/p.mass^2-k₀ → ∀ᶠ t in 𝓝[>] (0:ℝ), quotient (p.power (1+t))<k₀) ∧
    (deficit p.value/p.mass^2-k₀<0 → ∀ᶠ t in 𝓝[>] (0:ℝ), k₀<quotient (p.power (1+t))) := by sorry

end Liu
end
