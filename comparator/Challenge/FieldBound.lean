import Challenge.FinitePart
import Challenge.Pick
import Challenge.PickSums
import Challenge.Projection
import Challenge.Reproducing
import Challenge.LogSource

/- Frozen input: Liu/FieldBound.lean -/
noncomputable section
open Set MeasureTheory Real Filter
open scoped Topology ComplexConjugate
namespace Liu

theorem PickSum.potential_lipschitz {n : ℕ} (p : PickSum n) :
    ∃ C ≥ 0, ∀ x ∈ upper, ∀ y ∈ upper, ‖potential p.value x-potential p.value y‖ ≤ C*‖x-y‖ := by sorry

end Liu
end
