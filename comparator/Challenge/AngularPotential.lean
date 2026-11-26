import Challenge.RadialEnergy
import Challenge.Pick
import Challenge.PickSums
import Challenge.Projection
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Challenge.FieldBound
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Challenge.BoundaryField

/- Frozen input: Liu/AngularPotential.lean -/
noncomputable section
open Set MeasureTheory Real
open scoped ComplexConjugate
namespace Liu

def upperAngle (z : ℂ) := π/2+(Complex.log (-Complex.I*z)).im

def angularPotential (m : ℝ) (z : ℂ) : ℂ :=
  Complex.I*((m/2*upperAngle z*(π-upperAngle z):ℝ):ℂ)

end Liu
end
