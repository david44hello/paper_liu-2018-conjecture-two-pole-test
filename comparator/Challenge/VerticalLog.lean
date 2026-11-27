module

public import Challenge.PickRationalLog

@[expose] public section

/- Frozen input: Liu/VerticalLog.lean -/
noncomputable section
open Complex Real Set
open scoped ComplexConjugate
namespace Liu

def lowerNodeLog (z : ℂ) := Complex.log (-I*z) + (π/2:ℝ)*I

def upperNodeLog (z : ℂ) := Complex.log (I*z) - (π/2:ℝ)*I

end Liu
end
