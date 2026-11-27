module

public import Liu.FrozenFieldLimit

@[expose] public section

noncomputable section
open Set MeasureTheory Real Filter Metric
open scoped ComplexConjugate Topology
namespace Liu

/-- Convergence of the physical frozen numerator on every bounded half-disc. -/
theorem PickSum.compact_frozen_energy_limit {n : ℕ} (p : PickSum n) (R : ℝ) :
    Tendsto (fun t : ℝ => ∫ z in halfDisc R, ‖canonicalField (p.frozenLogSource t) z‖^2 -
      k₀*‖p.power (1+t) z‖^2 ∂area) (𝓝[>] 0) (𝓝 (-truncatedDeficit p.value R)) := by
  obtain ⟨C,hC,hb⟩ := p.frozenField_uniform_bound
  let M := max 1 p.bound
  have hM : 1≤M := le_max_left ..
  let D := halfDisc R
  have hD : MeasurableSet D := upper_open.measurableSet.inter isOpen_ball.measurableSet
  letI : IsFiniteMeasureOnCompacts area := IsFiniteMeasureOnCompacts.smul volume ENNReal.ofReal_ne_top
  have hfin := measure_ne_top_of_subset (μ:=area) (show D ⊆ ball 0 R from inter_subset_right) (measure_ball_lt_top ..).ne
  have hmaj : IntegrableOn (fun _ : ℂ => C^2+|k₀| *(M^2)^2) D area := integrableOn_const hfin
  have h0 : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have ht : ∀ᶠ t in 𝓝[>] (0:ℝ), t∈Ioo (0:ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0),h0.eventually_lt_const zero_lt_one] with t hl hr using ⟨hl,hr⟩
  have heq : -truncatedDeficit p.value R = ∫ z in D, ‖field p.value z‖^2-k₀*‖p.value z‖^2 ∂area := by
    rw [truncatedDeficit,←integral_neg]
    apply integral_congr_ae; filter_upwards with z; ring
  rw [heq]
  refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ hmaj ?_
  · filter_upwards [ht] with t htt
    have hc := canonicalField_continuous (p.supercritical_sources htt.1 htt.2).2.green.quadratic
    exact ((hc.measurable.norm.pow_const 2).sub ((p.power_measurable (1+t)).norm.pow_const 2 |>.const_mul k₀)).aestronglyMeasurable
  · filter_upwards [ht] with t htt
    filter_upwards [ae_restrict_mem (μ:=area) hD] with z hz
    have hy : 0≤z.im := le_of_lt hz.1
    have hv := (p.global_decay hy).trans ((div_le_self p.bound_pos.le (by linarith [norm_nonneg z])).trans (le_max_right 1 p.bound))
    have hp : ‖p.power (1+t) z‖ ≤ M^2 := by
      change ‖p.value z^((1+t:ℝ):ℂ)‖≤M^2
      rw [Complex.norm_cpow_real]
      apply (rpow_le_rpow (norm_nonneg _) hv (by linarith [htt.1])).trans
      simpa only [rpow_ofNat] using rpow_le_rpow_of_exponent_le hM (by linarith [htt.2] : 1+t≤(2:ℝ))
    apply (norm_sub_le ..).trans
    simp only [Real.norm_eq_abs,abs_mul,abs_pow,abs_of_nonneg (norm_nonneg _)]
    exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) (hb t ⟨htt.1.le,htt.2.le⟩ z hy) 2)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hp 2) (abs_nonneg _))
  · filter_upwards [ae_restrict_mem (μ:=area) hD] with z hz
    have hy : 0≤z.im := le_of_lt hz.1
    have hn : p.value z ≠ 0 := fun he => by have hi := p.value_im_pos hy; simp [he] at hi
    have hp := (Complex.hasStrictDerivAt_const_cpow (y:=(1:ℂ)) (Or.inl hn)).hasDerivAt.comp_ofReal.continuousAt
    have hl : Tendsto (fun t : ℝ => 1+t) (𝓝[>] 0) (𝓝 (1:ℝ)) := by simpa using h0.const_add 1
    have hpow : Tendsto (fun t : ℝ => p.power (1+t) z) (𝓝[>] 0) (𝓝 (p.value z)) := by
      simpa [PickSum.power,Function.comp_def] using hp.tendsto.comp hl
    simpa only [norm_mul,norm_neg,Complex.norm_I,one_mul] using
      (((p.frozenField_limit hy).norm.pow 2).sub ((hpow.norm.pow 2).const_mul k₀))

end Liu
