import Challenge.AngularDeficit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Challenge.AngularPotential
import Challenge.LogSource
import Challenge.SupercriticalEnergy
import Challenge.ProjectionKernel
import Challenge.QuotientDomain
import Challenge.PickSums
import Challenge.RadialEnergy
import Challenge.FinitePart
import Challenge.Pick
import Challenge.Projection
import Challenge.Reproducing
import Challenge.FarFieldClaim
import Challenge.CanonicalField
import Challenge.Orthogonality
import Challenge.FieldComparison
import Challenge.WitnessClaim
import Challenge.FinitePartLaws

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
