module

public import Challenge.QuotientDomain
public import Challenge.PickSums
public import Challenge.Pick
public import Challenge.Projection

@[expose] public section

/- Frozen input: Liu/LogSource.lean -/
noncomputable section
open Set MeasureTheory
open scoped ComplexConjugate
namespace Liu

def dbar (f : ℂ → ℂ) (z : ℂ) : ℂ :=
    ((fderiv ℝ f z) 1 + Complex.I*(fderiv ℝ f z) Complex.I)/2

end Liu
end
