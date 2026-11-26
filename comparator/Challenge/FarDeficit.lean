import Challenge.FieldBound
import Challenge.DeficitRemainder

/- Frozen input: Liu/FarDeficit.lean -/
noncomputable section
open Set MeasureTheory Real Metric
open scoped ComplexConjugate
namespace Liu

def fieldFarModel (m : ℝ) (z : ℂ) : ℂ := ((-m*(π/2-z.arg):ℝ):ℂ)/z

end Liu
end
