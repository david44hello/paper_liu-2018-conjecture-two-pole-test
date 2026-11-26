import Challenge.SingleTrace
import Challenge.Mass
import Challenge.IsolatedBounds

/- Frozen input: Liu/SingleFlux.lean -/
noncomputable section
open Set MeasureTheory Real
namespace Liu

theorem single_pole_flux_zero (a : ℝ) {m b : ℝ} (hm : 0 < m) (hb : 0 < b) :
    (∫ x : ℝ, ‖field (pole m ((a:ℂ)-(b:ℂ)*Complex.I)) x‖^2 -
      k₀*‖pole m ((a:ℂ)-(b:ℂ)*Complex.I) x‖^2)/π = 0 := by sorry

end Liu
end
