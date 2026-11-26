import Liu.TrialDensity
import Liu.ProjectionKernel

noncomputable section
open Set Real Complex Filter MeasureTheory
open scoped Topology ComplexConjugate
namespace Liu

/-- The two endpoint moments and relative bound used for a symmetric exponent window. -/
structure TrialWindow (F G : ℂ → ℂ) (η C : ℝ) : Prop where
  radius : 0<η
  small : η≤1
  constant_nonneg : 0≤C
  input : MemLp F 2 upperArea
  direction : MemLp G 2 upperArea
  nonzero : ∀ᵐ z ∂upperArea, F z≠0
  ratio : ∀ᵐ z ∂upperArea, ‖G z/F z‖≤C*(1+|Real.log ‖F z‖|)
  lower : Integrable (fun z => ‖F z‖^(2-η)*(1+|Real.log ‖F z‖|)^5) upperArea
  higher : Integrable (fun z => ‖F z‖^(2+η)*(1+|Real.log ‖F z‖|)^5) upperArea

section
variable {F G : ℂ → ℂ} {η C : ℝ} (h : TrialWindow F G η C)
include h

theorem TrialWindow.weight_integrable : Integrable (fun z => trialWeight ‖F z‖ η*(1+|Real.log ‖F z‖|)^5) upperArea := by
  simp only [trialWeight,add_mul]; exact h.lower.add h.higher

private theorem TrialWindow.density_meas (d : ℝ) :
    AEStronglyMeasurable (fun z => trialDensity (F z) (G z) d) upperArea := by
  have hf := h.input.aestronglyMeasurable.aemeasurable
  have hg := h.direction.aestronglyMeasurable.aemeasurable
  apply AEMeasurable.aestronglyMeasurable
  unfold trialDensity
  fun_prop

theorem TrialWindow.density_integrable {d : ℝ} (hd : |d|≤η) :
    Integrable (fun z => trialDensity (F z) (G z) d) upperArea := by
  apply (h.weight_integrable.const_mul (100*(1+C)^3+2*C)).mono' (h.density_meas d)
  filter_upwards [h.nonzero,h.ratio] with z hf hg
  exact trialDensity_bound hf h.constant_nonneg hg hd h.small

theorem TrialWindow.near_window : ∀ᶠ d : ℝ in 𝓝[≠] 0, |d|≤η := by
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0:ℝ) h.radius)] with d hd
  exact (show |d|<η by simpa [Real.dist_eq] using hd).le

theorem TrialWindow.density_integral_limit :
    Tendsto (fun d => ∫ z, trialDensity (F z) (G z) d ∂upperArea) (𝓝[≠] 0)
      (𝓝 (∫ z, ‖G z‖^2-(G z*conj (F z)).re-2*Real.log ‖F z‖*(G z*conj (F z)).re ∂upperArea)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun z => (100*(1+C)^3+2*C)*(trialWeight ‖F z‖ η*(1+|Real.log ‖F z‖|)^5))
  · exact .of_forall h.density_meas
  · filter_upwards [h.near_window] with d hd
    filter_upwards [h.nonzero,h.ratio] with z hf hg
    exact trialDensity_bound hf h.constant_nonneg hg hd h.small
  · exact h.weight_integrable.const_mul _
  · filter_upwards [h.nonzero] with z hf using trialDensity_limit hf (G z)

private theorem TrialWindow.power_bound {d : ℝ} (hd : |d|≤η) :
    ∀ᵐ z ∂upperArea, ‖‖F z‖^(2+d)‖≤trialWeight ‖F z‖ η*(1+|Real.log ‖F z‖|)^5 := by
  filter_upwards [h.nonzero] with z hz
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  have hb := trialWeight_bound (norm_pos_iff.mpr hz) hd
  have h₁ : (1:ℝ)≤(1+|Real.log ‖F z‖|)^5 := one_le_pow₀ (by linarith [abs_nonneg (Real.log ‖F z‖)])
  exact hb.trans (le_mul_of_one_le_right ((Real.rpow_nonneg (norm_nonneg _) _).trans hb) h₁)

theorem TrialWindow.power_integrable {d : ℝ} (hd : |d|≤η) :
    Integrable (fun z => ‖F z‖^(2+d)) upperArea :=
  h.weight_integrable.mono' ((h.input.aestronglyMeasurable.norm.aemeasurable.pow_const _).aestronglyMeasurable) (h.power_bound hd)

theorem TrialWindow.power_integral_limit :
    Tendsto (fun d : ℝ => ∫ z, ‖F z‖^(2+d) ∂upperArea) (𝓝[≠] 0) (𝓝 (energy F)) := by
  rw [energy_eq_integral h.input]
  apply tendsto_integral_filter_of_dominated_convergence
    (fun z => trialWeight ‖F z‖ η*(1+|Real.log ‖F z‖|)^5)
  · exact .of_forall fun d => (h.input.aestronglyMeasurable.norm.aemeasurable.pow_const _).aestronglyMeasurable
  · exact h.near_window.mono fun d hd => h.power_bound hd
  · exact h.weight_integrable
  · filter_upwards [h.nonzero] with z hz
    have ha := norm_pos_iff.mpr hz
    have hc : Continuous (fun d : ℝ => ‖F z‖^(2+d)) := by fun_prop (disch := positivity)
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

end
end Liu
