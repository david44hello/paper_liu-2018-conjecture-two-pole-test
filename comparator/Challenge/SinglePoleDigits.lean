module

public import Challenge.Mass
public import Mathlib.Analysis.PSeries

@[expose] public section

/- Frozen input: Liu/SinglePoleDigits.lean -/
noncomputable section
open Set Real Filter Finset
open scoped Topology
namespace Liu

theorem single_pole_decimal_bounds :
    0.901542676<singleConstant ∧ singleConstant<0.901542679 ∧
    0.0790756<singleConstant-k₀ ∧ singleConstant-k₀<0.0790757 ∧
    -0.1581513<2*k₀-2*singleConstant ∧ 2*k₀-2*singleConstant< -0.1581512 := by sorry

end Liu
end
