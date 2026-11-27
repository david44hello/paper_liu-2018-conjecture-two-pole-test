module

public import Challenge.RadialEnergy
public import Challenge.Pick
public import Challenge.PickSums
public import Challenge.Projection
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Challenge.FieldBound
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Challenge.BoundaryField
public import Challenge.LogSource
public import Challenge.QuotientDomain
public import Challenge.FarDeficit
public import Challenge.PoissonLine

@[expose] public section

/- Frozen input: Liu/RadialField.lean -/
noncomputable section
open Set MeasureTheory Real Filter
open scoped Topology ComplexConjugate
namespace Liu

theorem PickSum.finite_part {n : ℕ} (p : PickSum n) :
    finitePartExists p.value ∧ deficit p.value=∫ z, finitePartRemainder p.value p.mass z ∂upperArea := by sorry

end Liu
end
