module

public import Challenge.Pick

@[expose] public section

/- Frozen input: Liu/Mass.lean -/
noncomputable section
open Finset
namespace Liu

def singleConstant : ℝ := (3/4:ℝ)*∑' n : ℕ, 1 / (n:ℝ)^3

end Liu
end
