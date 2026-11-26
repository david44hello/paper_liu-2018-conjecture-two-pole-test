import Challenge.Anchor

/- Frozen input: Liu/ReciprocalTail.lean -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Liu

def topExtension (s γ T : ℝ) : Prop :=
  ∃ g : ℝ → ℝ, ContinuousOn g (Icc 0 (1/T)) ∧
    ∀ t : ℝ, T ≤ t → t^2*flux s γ t = g (1/t)

theorem top_flux_bounded {s γ T : ℝ} (hT : 0<T) (he : topExtension s γ T) :
    ∃ M : ℝ, 0≤M ∧ ∀ t : ℝ, T ≤ t → |flux s γ t| ≤ M/t^2 := by sorry

theorem integrable_flux_tail {s γ T u : ℝ} (hT : 0<T) (hu : 0<u)
    (hg : γ ∈ Icc 0 (Real.pi/2)) (hf : Certificate.fluxIdentity)
    (hc : ContinuousOn (flux s γ) (Ioi 0)) (he : topExtension s γ T) :
    IntegrableOn (flux s γ) (Ioi u) := by sorry

end Liu
end
