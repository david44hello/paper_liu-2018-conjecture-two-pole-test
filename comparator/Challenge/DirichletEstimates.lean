import Challenge.DirichletDerivatives
import Challenge.FieldComparison
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Challenge.FieldBound
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/- Frozen input: Liu/DirichletEstimates.lean -/
noncomputable section
open Set Metric Filter Real Complex MeasureTheory
open scoped Topology ContDiff InnerProductSpace
namespace Liu

def dirichletAnnulus (r : ℝ) := {w∈upper | r/4<‖w‖ ∧ ‖w‖<2*r}

theorem dirichlet_annular_gradient :
    ∃ C>0, ∀ V : ℂ → ℂ, ContDiffOn ℝ ∞ V closedUpper → (∀ x : ℝ, V x=0) →
    ∀ z∈closedUpper, 0<‖z‖ →
      ‖fderivWithin ℝ V closedUpper z‖ ≤ C*(‖z‖⁻¹*sSup ((fun w => ‖V w‖) '' dirichletAnnulus ‖z‖)+
        ‖z‖*sSup ((fun w => ‖Laplacian.laplacian V w‖) '' dirichletAnnulus ‖z‖)) := by sorry

theorem dirichlet_cubic_decay {B : ℝ} (hB : 0≤B) :
    ∃ C>0, ∀ V : ℂ → ℂ, ContDiffOn ℝ ∞ V closedUpper → (∀ x : ℝ, V x=0) →
      (∃ M≥0, ∀ w∈upper, ‖V w‖≤M) →
      (∀ w∈upper, ‖Laplacian.laplacian V w‖≤B/(1+‖w‖)^3) →
      ∀ z∈closedUpper, 1<‖z‖ →
        ‖V z‖≤C*(1+Real.log ‖z‖)/‖z‖ ∧
        ‖fderivWithin ℝ V closedUpper z‖≤C*(1+Real.log ‖z‖)/‖z‖^2 := by sorry

end Liu
end
