import Challenge.ChebyshevEllipse
import Challenge.ChebyshevAlias
import Mathlib.Analysis.Fourier.AddCircle

/- Frozen input: Liu/ChebyshevApproximation.lean -/
noncomputable section
open Real Set Polynomial Polynomial.Chebyshev
namespace Liu

theorem firstKind_ellipse_error {χ : ℂ → ℂ} {ρ M : ℝ} (hρ : 1<ρ)
    (ha : AnalyticOnNhd ℂ χ (bernsteinEllipse ρ)) (hM : ∀ z∈bernsteinEllipse ρ, ‖χ z‖≤M)
    (n : ℕ) {x : ℝ} (hx : x∈Icc (-1:ℝ) 1) :
    ‖χ x-(firstKindInterpolant n χ).eval (x:ℂ)‖≤4*M/(ρ^n*(ρ-1)) := by sorry

end Liu
end
