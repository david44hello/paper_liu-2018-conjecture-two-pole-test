import Liu.LocalParameterDerivative

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology
namespace Liu

/-- Local version of differentiation under a dominated holomorphic integral.
The majorant and its parameter neighborhood may depend on the center. -/
theorem differentiableOn_local_integral {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {U : Set ℂ} (hU : IsOpen U) {F : ℂ → α → ℂ}
    (hm : ∀ w, AEStronglyMeasurable (F w) μ)
    (hd : ∀ᵐ t ∂μ, DifferentiableOn ℂ (fun w => F w t) U)
    (hb : ∀ c ∈ U, ∃ M : α → ℝ, Integrable M μ ∧
      ∃ V ∈ 𝓝 c, ∀ᵐ t ∂μ, ∀ w ∈ V, ‖F w t‖ ≤ M t) :
    DifferentiableOn ℂ (fun w => ∫ t, F w t ∂μ) U := by
  intro c hc
  obtain ⟨M,hI,V,hV,hM⟩ := hb c hc
  exact (hasDerivAt_local_integral μ hU hc hm hd hI hV hM).differentiableAt.differentiableWithinAt

end Liu
