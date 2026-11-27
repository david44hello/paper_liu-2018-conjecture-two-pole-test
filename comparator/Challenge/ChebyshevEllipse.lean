module

public import Mathlib

@[expose] public section

/- Frozen input: Liu/ChebyshevEllipse.lean -/
noncomputable section
open Set Real Metric Complex
open scoped Topology Interval Real
namespace Liu

def bernsteinEllipse (ρ : ℝ) : Set ℂ := {z | ‖z-1‖+‖z+1‖≤ρ+ρ⁻¹}

end Liu
end
