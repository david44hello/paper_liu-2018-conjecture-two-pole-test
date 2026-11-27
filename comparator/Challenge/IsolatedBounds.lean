module

public import Challenge.SingleTrace

@[expose] public section

/- Frozen input: Liu/IsolatedBounds.lean -/
noncomputable section
open Set MeasureTheory Real
namespace Liu

theorem isolatedTrace_le_depth (a x : ℝ) {b : ℝ} (hb : 0 < b) : isolatedTrace a b x ≤ 1/b := by sorry

theorem isolatedTrace_le_distance (a x : ℝ) {b : ℝ} (hb : 0 < b) (hx : x ≠ a) :
    isolatedTrace a b x ≤ π/(2*|x-a|) := by sorry

end Liu
end
