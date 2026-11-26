import Challenge.RadialEnergy
import Challenge.Pick
import Challenge.PickSums
import Challenge.Projection
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Challenge.FieldBound
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Challenge.BoundaryField
import Challenge.LogSource
import Challenge.QuotientDomain
import Challenge.FarDeficit
import Challenge.PoissonLine

/- Frozen input: Liu/RadialField.lean -/
noncomputable section
open Set MeasureTheory Real Filter
open scoped Topology ComplexConjugate
namespace Liu

theorem PickSum.finite_part {n : ℕ} (p : PickSum n) :
    finitePartExists p.value ∧ deficit p.value=∫ z, finitePartRemainder p.value p.mass z ∂upperArea := by sorry

end Liu
end
