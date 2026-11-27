module

public import Challenge.TrialOrthogonality
public import Challenge.BergmanLpNorm

@[expose] public section

/- Frozen input: Liu/LiuComparison.lean -/
noncomputable section
open Set Filter MeasureTheory Real Complex
open scoped Topology ENNReal
namespace Liu

theorem liu_norm_comparison {F : ℂ → ℂ}
    (hF : MemLp F 2 upperArea) (hhol : DifferentiableOn ℂ F upper)
    (hn : ∀ z ∈ upper, F z≠0) {η₀ C : ℝ} (hη : 0<η₀) (hC : 0<C)
    (hm : ∀ p : ℝ, |p-2|≤η₀ →
      Integrable (fun z => ‖F z‖^p*(1+|Real.log ‖F z‖|)^5) upperArea)
    (hg : ∀ᵐ z ∂upperArea, ‖(asL2 (logInput F)-project (asL2 (logInput F))) z‖ ≤
      C*‖F z‖*(1+|Real.log ‖F z‖|)) :
    (∀ p : ℕ → ℝ, Tendsto p atTop (𝓝 2) → (∀ n, p n≠2) →
      (∀ n, bergmanLpNorm (p n)≤ENNReal.ofReal (liuNorm (p n))) → quotient F≤k₀) ∧
    (k₀<quotient F → ∀ᶠ p in 𝓝[≠] (2:ℝ), ENNReal.ofReal (liuNorm p)<bergmanLpNorm p) := by sorry

end Liu
end
