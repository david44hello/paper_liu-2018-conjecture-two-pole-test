import Challenge.ReciprocalModel
import Challenge.ReciprocalTail

/- Frozen input: Liu/ReciprocalDisc.lean -/
noncomputable section
open Set Real MeasureTheory Filter Metric
open scoped Topology
namespace Liu

theorem top_reciprocal_lemma (s γ : ℝ) (hg : γ∈Icc 0 π) :
    (∀ u : ℝ, 0<u → u^2*flux s γ u=(1/u)⁻¹*boundaryFlux (unitDepthSum s γ (1/u))) ∧
    (∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (ball 0 1) ∧ ∀ v : ℝ, 0<v → v<1 →
      G v=((v⁻¹*boundaryFlux (unitDepthSum s γ v):ℝ):ℂ)) ∧
    (∃ M : ℝ, 0≤M ∧ ∀ u : ℝ, exp (1/2)≤u → |u^2*flux s γ u|≤M) := by sorry

end Liu
end
