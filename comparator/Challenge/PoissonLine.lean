import Challenge.QuotientDomain
import Challenge.PickSums
import Mathlib.Probability.Distributions.Cauchy
import Challenge.CrossClaim

/- Frozen input: Liu/PoissonLine.lean -/
noncomputable section
open Set MeasureTheory Filter Real
open scoped Topology ComplexConjugate
namespace Liu

def poissonLine (a b x : ℝ) := b/((x-a)^2+b^2)

end Liu
end
