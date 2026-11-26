import Liu.Denominator
import Mathlib.Analysis.Complex.MeanValue

noncomputable section
open Set MeasureTheory Real Metric
namespace Liu

private theorem polar_circle (v : ℝ × ℝ) (z : ℂ) :
    Complex.polarCoord.symm v+z = circleMap z v.1 v.2 := by
  rw [Complex.polarCoord_symm_apply,circleMap,Complex.exp_mul_I]
  simp [←Complex.ofReal_cos,←Complex.ofReal_sin,add_comm]

private theorem disc_mean_angle {f : ℂ → ℂ} {z : ℂ} {r : ℝ} (hr : 0<r)
    (hd : DiffContOnCl ℂ f (ball z r)) :
    (∫ t in Ioo (-π) π, f (circleMap z r t)) = ((2*π:ℝ):ℂ)*f z := by
  have h := (show DiffContOnCl ℂ f (ball z |r|) by simpa [abs_of_pos hr] using hd).circleAverage
  unfold circleAverage at h
  have hc := (periodic_circleMap z r).comp f
  have hper := hc.intervalIntegral_add_eq (-π) 0
  rw [show -π+2*π = π by ring,zero_add] at hper
  simp only [Function.comp_apply] at hper
  rw [←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le (by linarith [pi_pos]),
    hper]
  rw [←h,Complex.real_smul]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr pi_ne_zero]

/-- The disc mean formula for normalized plane area. All regularity is local
to the closed disc, including when the given function has poles elsewhere. -/
theorem holomorphic_disc_mean {f : ℂ → ℂ} {z : ℂ} {R : ℝ} (hR : 0<R)
    (hd : DifferentiableOn ℂ f (ball z R)) (hc : ContinuousOn f (closedBall z R)) :
    (∫ w in ball z R, f w ∂area) = ((R^2:ℝ):ℂ)*f z := by
  classical
  let θ := Ioo (-π) π
  let D := Ioo (0:ℝ) R ×ˢ θ
  let K := Icc (0:ℝ) R ×ˢ Icc (-π) π
  let G := fun v : ℝ × ℝ => (v.1:ℂ)*f (circleMap z v.1 v.2)
  have tr := (measurePreserving_add_right (volume:Measure ℂ) z).setIntegral_preimage_emb
    (Homeomorph.addRight z).measurableEmbedding f (ball z R)
  have hp : (fun w : ℂ => w+z) ⁻¹' ball z R = ball 0 R := by ext w; simp [Metric.mem_ball,dist_eq_norm]
  rw [hp] at tr
  have hpolar : ∫ w in ball z R, f w = ∫ v in D, G v := by
    rw [←tr,←integral_indicator Metric.isOpen_ball.measurableSet,←Complex.integral_comp_polarCoord_symm,polarCoord_target]
    have hs : D ⊆ Ioi (0:ℝ) ×ˢ θ := fun v hv => ⟨hv.1.1,hv.2⟩
    rw [←inter_eq_right.mpr hs,←setIntegral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)]
    apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    intro v hv
    dsimp only
    have hnorm : ‖Complex.polarCoord.symm v‖ = v.1 := by rw [Complex.norm_polarCoord_symm,abs_of_pos hv.1]
    by_cases hr : v.1<R
    · have hball : Complex.polarCoord.symm v ∈ ball 0 R := by simpa only [Metric.mem_ball,dist_zero_right,hnorm] using hr
      have hrect : v ∈ Ioo (0:ℝ) R ×ˢ Ioo (-π) π := ⟨⟨hv.1,hr⟩,hv.2⟩
      simp only [indicator_of_mem hball,indicator_of_mem hrect,G,polar_circle,Complex.real_smul]
    · have hball : Complex.polarCoord.symm v ∉ ball 0 R := by simpa only [Metric.mem_ball,dist_zero_right,hnorm] using hr
      have hrect : v ∉ Ioo (0:ℝ) R ×ˢ Ioo (-π) π := fun h => hr h.1.2
      simp only [indicator_of_notMem hball,indicator_of_notMem hrect,smul_zero]
  have hcurve : Continuous (fun v : ℝ × ℝ => circleMap z v.1 v.2) := by unfold circleMap; fun_prop
  have hK : MapsTo (fun v : ℝ × ℝ => circleMap z v.1 v.2) K (closedBall z R) := by
    intro v hv
    change dist (circleMap z v.1 v.2) z ≤ R
    simpa [dist_eq_norm,circleMap,abs_of_nonneg hv.1.1] using hv.1.2
  have hG : IntegrableOn G D (volume.prod volume) := by
    have H : ContinuousOn G K := (Complex.continuous_ofReal.comp continuous_fst).continuousOn.mul
      (hc.comp hcurve.continuousOn hK)
    exact (H.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  unfold area
  rw [Measure.restrict_smul,integral_smul_measure,ENNReal.toReal_ofReal (by positivity),hpolar]
  have hsep : (∫ v in D, G v) = ((R^2/2:ℝ):ℂ)*(((2*π:ℝ):ℂ)*f z) := by
    rw [Measure.volume_eq_prod,setIntegral_prod G hG]
    calc
      _ = ∫ r in Ioo (0:ℝ) R, (r:ℂ)*(((2*π:ℝ):ℂ)*f z) := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro r hr
        change (∫ t in θ, (r:ℂ)*f (circleMap z r t)) = _
        rw [integral_const_mul]
        congr 1
        have hcl := closure_ball_subset_closedBall (x:=z) (ε:=r)
        exact disc_mean_angle hr.1 ⟨hd.mono (ball_subset_ball hr.2.le),hc.mono (hcl.trans (closedBall_subset_closedBall hr.2.le))⟩
      _ = _ := by
        rw [integral_mul_const,integral_complex_ofReal,←integral_Ioc_eq_integral_Ioo,
          ←intervalIntegral.integral_of_le hR.le,integral_id]
        simp
  rw [hsep,Complex.real_smul]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr pi_ne_zero]
  <;> ring

end Liu
