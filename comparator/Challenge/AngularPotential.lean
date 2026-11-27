module

public import Challenge.RadialEnergy
public import Challenge.Pick
public import Challenge.PickSums
public import Challenge.Projection
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Challenge.FieldBound
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Challenge.BoundaryField

@[expose] public section

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
