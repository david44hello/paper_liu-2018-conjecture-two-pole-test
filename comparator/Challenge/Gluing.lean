import Challenge.BetaLedger
import Mathlib

/- Frozen input: Liu/Gluing.lean -/
noncomputable section
open MeasureTheory Set Filter
namespace Liu.Certificate

def boxBounds : Prop :=
  ∀ b ∈ boxes, ∀ s γ : ℝ, b.contains s γ → γ ≤ Real.pi/2 →
    (∀ u : ℝ, b.depth ≤ u → 0 < margin s γ u) ∧
      (b.safeLower:ℝ) ≤ margin s γ b.depth

def fluxIdentity : Prop :=
  ∀ s γ : ℝ, γ ∈ Icc 0 (Real.pi/2) → ∀ u v : ℝ, 0 < u → u ≤ v →
    IntervalIntegrable (flux s γ) volume u v ∧
    margin s γ u = margin s γ v - ∫ t in u..v, flux s γ t

def prefixProperty : Prop :=
  ∀ b ∈ boxes, ∀ s γ : ℝ, b.contains s γ → γ ∈ Icc 0 (Real.pi/2) →
    ∀ u : ℝ, 0 < u → u ≤ b.depth →
      (∫ t in u..b.depth, |flux s γ t|) ≤ b.beta

end Liu.Certificate
end
