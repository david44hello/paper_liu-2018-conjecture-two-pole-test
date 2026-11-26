import Challenge.Pick

/- Frozen input: Liu/CrossSource.lean -/
noncomputable section
open scoped ComplexConjugate
namespace Liu

def edgeSum (a : ℝ) (q z : ℂ) : ℂ :=
  -(a:ℂ)/z - (1-(a:ℂ))/(z-q)

def crossSource (a : ℝ) (q z : ℂ) : ℂ :=
  edgeSum a q z / conj (edgeSum a q z) * conj (deriv (edgeSum a q) z)
  - (a/‖z‖^2:ℝ) - ((1-a)/‖z-q‖^2:ℝ)

end Liu
end
