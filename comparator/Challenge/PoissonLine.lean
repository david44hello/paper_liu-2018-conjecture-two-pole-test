module

public import Challenge.QuotientDomain
public import Challenge.PickSums
public import Mathlib.Probability.Distributions.Cauchy
public import Challenge.CrossClaim

@[expose] public section

/- Frozen input: Liu/PoissonLine.lean -/
noncomputable section
open Set MeasureTheory Filter Real
open scoped Topology ComplexConjugate
namespace Liu

def poissonLine (a b x : ℝ) := b/((x-a)^2+b^2)

end Liu
end
