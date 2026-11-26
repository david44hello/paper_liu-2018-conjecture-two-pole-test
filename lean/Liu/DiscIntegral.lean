import Liu.Cayley

noncomputable section
open Set MeasureTheory Metric Filter Real
open scoped Topology ComplexConjugate
namespace Liu

theorem cayley_integrable_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {z : ℂ} (hz : z ∈ upper) (f : ℂ → E) :
    IntegrableOn f upper area ↔ IntegrableOn (fun w => ‖cayleyJac z w‖^2 • f (cayley z w)) disc area := by
  have hj := cayley_bijOn hz
  have hd (w : ℂ) (hw : w ∈ disc) : HasFDerivWithinAt (cayley z) (cayleyRealDerivative z w) disc w :=
    ((cayley_deriv z hw).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have h := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume (s:=disc) Metric.isOpen_ball.measurableSet hd hj.injOn f
  rw [hj.image_eq] at h
  simp_rw [cayley_det] at h
  unfold IntegrableOn area
  simp only [Measure.restrict_smul,integrable_smul_measure (ENNReal.ofReal_ne_zero_iff.mpr (by positivity : 0 < 1/π)) ENNReal.ofReal_ne_top]
  exact h

theorem disc_mean_integrable {f : ℂ → ℂ} (hf : IntegrableOn f disc area) (hd : DifferentiableOn ℂ f disc) :
    ∫ w in disc, f w ∂area = f 0 := by
  classical
  let μ := area.restrict disc
  let I := fun r : ℝ => (ball (0:ℂ) r).indicator f
  have hr1 : Tendsto (fun r : ℝ => r) (𝓝[<] 1) (𝓝 1) := nhdsWithin_le_nhds
  have H : Tendsto (fun r : ℝ => ∫ w, I r w ∂μ) (𝓝[<] (1:ℝ)) (𝓝 (∫ w, f w ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun w => ‖f w‖) ?_ ?_ hf.norm ?_
    · exact Eventually.of_forall fun r => hf.aestronglyMeasurable.indicator Metric.isOpen_ball.measurableSet
    · exact Eventually.of_forall fun r => ae_of_all _ (fun w => norm_indicator_le_norm_self ..)
    · filter_upwards [ae_restrict_mem (μ:=area) Metric.isOpen_ball.measurableSet] with w hw
      change dist w 0 < 1 at hw
      have hh := hr1.eventually_const_lt hw
      apply tendsto_const_nhds.congr'
      filter_upwards [hh] with r hr
      exact (indicator_of_mem (show w ∈ ball (0:ℂ) r from hr) f).symm
  have H' : Tendsto (fun r : ℝ => ∫ w, I r w ∂μ) (𝓝[<] (1:ℝ)) (𝓝 (f 0)) := by
    have ht : Tendsto (fun r : ℝ => ((r^2:ℝ):ℂ)*f 0) (𝓝[<] 1) (𝓝 (f 0)) := by
      simpa using ((Complex.continuous_ofReal.continuousAt.tendsto.comp (hr1.pow 2)).mul_const (f 0))
    apply ht.congr'
    filter_upwards [hr1.eventually_const_lt zero_lt_one,self_mem_nhdsWithin (a:=(1:ℝ)) (s:=Iio 1)] with r hr htop
    have hsub : closedBall (0:ℂ) r ⊆ disc := closedBall_subset_ball htop
    have hd' := hd.mono (ball_subset_closedBall.trans hsub)
    have he := holomorphic_disc_mean hr hd' (hd.continuousOn.mono hsub)
    change _ = ∫ w, (ball (0:ℂ) r).indicator f w ∂area.restrict disc
    rw [integral_indicator Metric.isOpen_ball.measurableSet,Measure.restrict_restrict Metric.isOpen_ball.measurableSet,
      inter_eq_left.mpr (ball_subset_closedBall.trans hsub)]
    exact he.symm
  exact tendsto_nhds_unique H H'

end Liu
