module

public import Liu.DiscMean

@[expose] public section

noncomputable section
open Set MeasureTheory Real Metric
open scoped ComplexConjugate
namespace Liu

/-- Local point evaluation on actual analytic L² representatives. -/
theorem bergman_evaluation_bound {f : ℂ → ℂ} (hf : MemLp f 2 upperArea)
    (hd : DifferentiableOn ℂ f upper) {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : closedBall z r ⊆ upper) :
    r*‖f z‖ ≤ ‖asL2 f‖ := by
  letI : IsFiniteMeasureOnCompacts area := IsFiniteMeasureOnCompacts.smul volume ENNReal.ofReal_ne_top
  let D := ball z r
  have hU : D ⊆ upper := ball_subset_closedBall.trans hsub
  have hmean := holomorphic_disc_mean hr (hd.mono hU) (hd.continuousOn.mono hsub)
  have hconst := holomorphic_disc_mean (f:=fun _ => (1:ℂ)) (z:=z) hr (by fun_prop) (by fun_prop)
  have hfi : IntegrableOn f D area :=
    (hd.continuousOn.mono hsub |>.integrableOn_compact (isCompact_closedBall z r)).mono_set ball_subset_closedBall
  have hfi2 : Integrable (fun w => ‖f w‖^2) upperArea := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hsq : IntegrableOn (fun w => ‖f w‖^2) D area :=
    (show IntegrableOn _ upper area from hfi2).mono_set hU
  have harea : area.real D = r^2 := by
    simp [D,integral_const,Complex.real_smul] at hconst
    exact_mod_cast hconst
  let v := f z
  have inner (w : ℂ) : ‖f w-v‖^2 = ‖f w‖^2 - 2*(f w*conj v).re+‖v‖^2 := by
    simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.conj_re,Complex.conj_im]
    ring
  have hip : IntegrableOn (fun w => (f w*conj v).re) D area := Complex.reCLM.integrable_comp (hfi.mul_const _)
  have hc : IntegrableOn (fun _ : ℂ => ‖v‖^2) D area := by
    exact integrableOn_const (measure_ball_lt_top ..).ne
  have hlin : (∫ w in D, (f w*conj v).re ∂area) = r^2*‖v‖^2 := by
    have h := integral_re (hfi.mul_const (conj v))
    change (∫ w in D, (f w*conj v).re ∂area) = (∫ w in D, f w*conj v ∂area).re at h
    rw [h,integral_mul_const]
    change ((∫ w in ball z r, f w ∂area)*conj v).re = _
    rw [hmean,show f z=v from rfl,mul_assoc,Complex.mul_conj']
    norm_cast
  have hnon := setIntegral_nonneg (μ:=area) (s:=D) (f:=fun w => ‖f w-v‖^2)
    isOpen_ball.measurableSet (fun _ _ => sq_nonneg _)
  simp_rw [inner] at hnon
  have hdiff : IntegrableOn (fun w => ‖f w‖^2-2*(f w*conj v).re) D area := hsq.sub (hip.const_mul 2)
  rw [integral_add hdiff hc,integral_sub hsq (hip.const_mul 2),integral_const_mul,hlin,
    setIntegral_const,smul_eq_mul,harea] at hnon
  have hle : (∫ w in D, ‖f w‖^2 ∂area) ≤ ∫ w, ‖f w‖^2 ∂upperArea :=
    setIntegral_mono_set hfi2 (ae_of_all _ fun w => sq_nonneg _) (Filter.Eventually.of_forall hU)
  rw [←energy_eq_integral hf] at hle
  apply le_of_sq_le_sq _ (norm_nonneg _)
  change _ ≤ energy f
  rw [mul_pow]
  exact (show r^2*‖v‖^2 ≤ ∫ w in D, ‖f w‖^2 ∂area by linarith).trans hle

theorem ball_below_height {z w : ℂ} {r : ℝ} (hr : r < z.im) (hw : w ∈ closedBall z r) :
    w ∈ upper := by
  have h := Complex.abs_im_le_norm (w-z)
  rw [Complex.sub_im,←dist_eq_norm] at h
  have hdist : dist w z ≤ r := hw
  change 0<w.im
  linarith [(abs_le.mp h).1]

end Liu
