import Challenge.QuotientDomain
import Challenge.PickSums
import Challenge.Pick
import Challenge.Projection

/- Frozen input: Liu/LogSource.lean -/
noncomputable section
open Set MeasureTheory
open scoped ComplexConjugate
namespace Liu

def dbar (f : ℂ → ℂ) (z : ℂ) : ℂ :=
    ((fderiv ℝ f z) 1 + Complex.I*(fderiv ℝ f z) Complex.I)/2

end Liu
end
