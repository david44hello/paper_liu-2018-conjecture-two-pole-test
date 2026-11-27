module

public import Challenge.BoxData
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/- Frozen input: Liu/Cover.lean -/
noncomputable section
namespace Liu.Certificate

theorem cover {s γ : ℝ} (hs₁ : -(25/3:ℝ) ≤ s) (hs₂ : s ≤ 25/3)
    (hg₁ : 0 ≤ γ) (hg₂ : γ ≤ Real.pi / 2) : ∃ b ∈ boxes, b.contains s γ := by sorry

end Liu.Certificate
end
