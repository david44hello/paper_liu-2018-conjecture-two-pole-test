module

public import Challenge.Gluing

@[expose] public section

/- Frozen input: Liu/Prefix.lean -/
noncomputable section
open Set MeasureTheory
namespace Liu.Certificate

def smallMass (s : ℝ) : ℝ := min (normalMass s) (1-normalMass s)

def smallDepthEstimate : Prop :=
  ∀ s γ t : ℝ, γ ∈ Icc 0 (Real.pi/2) → 0 < t → t ≤ 1/4 →
    |flux s γ t| ≤ 2^34/(smallMass s)^2 * (1 + Real.log (1/t))

def mixedEdgeEstimate : Prop :=
  ∀ s γ : ℝ, γ ∈ Icc 0 (Real.pi/2) → 0 < Real.sin γ →
    ∃ c : ℝ, |c| ≤ 64/(Real.sin γ)^4 ∧ ∀ t : ℝ, 0 < t → t ≤ 1/4 →
      |flux s γ t - c * Real.log (1/t)| ≤ 4096 / ((normalMass s)^2 * (Real.sin γ)^8)

end Liu.Certificate
end
