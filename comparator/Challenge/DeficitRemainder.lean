import Challenge.AngularDeficit

/- Frozen input: Liu/DeficitRemainder.lean -/
noncomputable section
open Set MeasureTheory Filter Metric Real
open scoped Topology
namespace Liu

def finitePartRemainder (S : ℂ → ℂ) (m : ℝ) (z : ℂ) : ℝ :=
  (k₀*‖S z‖^2-‖field S z‖^2) - leadingDeficit m z

end Liu
end
