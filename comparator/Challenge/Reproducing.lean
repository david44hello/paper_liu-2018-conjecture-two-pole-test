module

public import Challenge.QuotientDomain
public import Challenge.PickSums
public import Challenge.RadialEnergy
public import Mathlib.Analysis.Complex.MeanValue
public import Challenge.BergmanClosed

@[expose] public section

/- Frozen input: Liu/Reproducing.lean -/
noncomputable section
open Set MeasureTheory Metric Real
open scoped ComplexConjugate
namespace Liu

def bergmanKernel (z w : ℂ) : ℂ := -((w-conj z)^2)⁻¹

end Liu
end
