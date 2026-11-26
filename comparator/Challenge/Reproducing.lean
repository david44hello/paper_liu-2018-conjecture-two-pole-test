import Challenge.QuotientDomain
import Challenge.PickSums
import Challenge.RadialEnergy
import Mathlib.Analysis.Complex.MeanValue
import Challenge.BergmanClosed

/- Frozen input: Liu/Reproducing.lean -/
noncomputable section
open Set MeasureTheory Metric Real
open scoped ComplexConjugate
namespace Liu

def bergmanKernel (z w : ℂ) : ℂ := -((w-conj z)^2)⁻¹

end Liu
end
