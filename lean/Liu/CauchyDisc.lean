import Liu.PolarRays
import Liu.DiscMean

noncomputable section
open Set MeasureTheory Real Metric
open scoped ComplexConjugate Topology
namespace Liu

private theorem circle_mean {f : ℂ → ℂ} {s : ℝ} (hs : 0<s) (hd : DiffContOnCl ℂ f (ball 0 s)) :
    (∫ θ in Ioo (-π) π, f (polarRay s θ)) = ((2*π:ℝ):ℂ)*f 0 := by
  have h := (show DiffContOnCl ℂ f (ball 0 |s|) by simpa [abs_of_pos hs] using hd).circleAverage
  unfold circleAverage at h
  have hper := ((periodic_circleMap 0 s).comp f).intervalIntegral_add_eq (-π) 0
  rw [show -π+2*π=π by ring,zero_add] at hper
  simp only [Function.comp_apply] at hper
  have he : polarRay s=circleMap (0:ℂ) s := by funext θ; simp [polarRay,unitPhase,circleMap]
  rw [he,←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le (by linarith [pi_pos]),hper,
    ←h,Complex.real_smul]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr pi_ne_zero]

private theorem cauchy_circle_inner (h : ℂ) {s : ℝ} (hs : 0<s) (hlt : s<‖h‖) :
    (∫ θ in Ioo (-π) π, (h-polarRay s θ)⁻¹)=((2*π:ℝ):ℂ)*h⁻¹ := by
  have hd (w : ℂ) (hw : w∈closedBall (0:ℂ) s) : DifferentiableAt ℂ (fun w => (h-w)⁻¹) w := by
    have hn : h-w≠0 := sub_ne_zero.mpr (by
      intro e; rw [←e] at hw
      have : ‖h‖≤ s := by simpa using hw
      linarith)
    fun_prop (disch := exact hn)
  simpa only [sub_zero] using circle_mean hs ⟨fun w hw => (hd w (ball_subset_closedBall hw)).differentiableWithinAt,
    fun w hw => (hd w (closure_ball_subset_closedBall hw)).continuousAt.continuousWithinAt⟩

private theorem cauchy_circle_outer (h : ℂ) {s : ℝ} (hlt : ‖h‖<s) :
    (∫ θ in Ioo (-π) π, (h-polarRay s θ)⁻¹)=0 := by
  have hs := (norm_nonneg h).trans_lt hlt
  let F := fun w : ℂ => -w/((s:ℂ)^2-conj h*w)
  have hn (w : ℂ) (hw : ‖w‖≤ s) : (s:ℂ)^2-conj h*w≠0 := by
    intro e
    have hh := congrArg norm (sub_eq_zero.mp e)
    rw [norm_pow,Complex.norm_of_nonneg hs.le,norm_mul,Complex.norm_conj] at hh
    nlinarith [mul_le_mul_of_nonneg_left hw (norm_nonneg h),mul_lt_mul_of_pos_right hlt hs]
  have dF (w : ℂ) (hw : w∈closedBall (0:ℂ) s) : DifferentiableAt ℂ F w := by
    dsimp [F]; fun_prop (disch := exact hn w (by simpa using hw))
  have hm : (∫ θ in Ioo (-π) π, F (polarRay s θ))=0 := by
    simpa [F] using circle_mean hs (f:=F) ⟨fun w hw => (dF w (ball_subset_closedBall hw)).differentiableWithinAt,
      fun w hw => (dF w (closure_ball_subset_closedBall hw)).continuousAt.continuousWithinAt⟩
  have he (θ : ℝ) : (h-polarRay s θ)⁻¹=conj (F (polarRay s θ)) := by
    let w := polarRay s θ
    have hw : ‖w‖=s := by dsimp only [w,polarRay]; rw [norm_mul,Complex.norm_of_nonneg hs.le,unitPhase_norm,mul_one]
    have hww : w*conj w=(s:ℂ)^2 := by rw [Complex.mul_conj',hw]
    have hsep : h-w≠0 := sub_ne_zero.mpr (by intro e; rw [e,hw] at hlt; exact (lt_irrefl _ hlt))
    have hconj : (s:ℂ)^2-h*conj w≠0 := by
      have hh := (map_ne_zero (starRingEnd ℂ)).mpr (hn w hw.le)
      simpa only [map_sub,map_pow,map_mul,Complex.conj_ofReal,Complex.conj_conj] using hh
    change (h-w)⁻¹=conj (F w)
    simp only [F,map_div₀,map_neg,map_sub,map_pow,map_mul,Complex.conj_ofReal,Complex.conj_conj]
    field_simp [hsep,hconj]; linear_combination -hww
  simp_rw [he,integral_conj,hm,map_zero]

private theorem origin_disc_cauchy {h : ℂ} {R : ℝ} (hR : 0<R) (hr : ‖h‖<R) :
    (∫ w in ball (0:ℂ) R, (h-w)⁻¹ ∂area)=conj h := by
  classical
  let f := fun w : ℂ => (ball (0:ℂ) R).indicator (fun w => (h-w)⁻¹) w
  let p := fun u : ℝ×ℝ => u.1 • f (Complex.polarCoord.symm u)
  let Ω := polarCoord.target
  have hf : Integrable f volume := by
    apply (integrable_indicator_iff Metric.isOpen_ball.measurableSet).mpr
    have hi := inverse_distance_integrable h (R+‖h‖+1)
    apply (hi.mono_set (show ball (0:ℂ) R ⊆ ball h (R+‖h‖+1) from fun w hw => by
      rw [mem_ball,dist_eq_norm]
      have hh : ‖w‖<R := by simpa using hw
      linarith [norm_sub_le w h])).mono' (by fun_prop)
    filter_upwards with w
    simp
  have hfm : Measurable f := (by unfold f; exact (by fun_prop : Measurable (fun w : ℂ => (h-w)⁻¹)).indicator Metric.isOpen_ball.measurableSet)
  have hp : IntegrableOn p Ω (volume.prod volume) := by
    have hm : Measurable p := by
      change Measurable (fun u : ℝ×ℝ => u.1 • f (Complex.polarCoord.symm u))
      simp_rw [polarRay_coord]; unfold polarRay unitPhase; fun_prop
    refine ⟨hm.aestronglyMeasurable,?_⟩
    have hi := hf.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_enorm,←Complex.lintegral_comp_polarCoord_symm (fun w => ‖f w‖ₑ)] at hi
    rw [hasFiniteIntegral_iff_enorm,←Measure.volume_eq_prod]
    apply lt_of_eq_of_lt _ hi
    apply setLIntegral_congr_fun polarCoord.open_target.measurableSet
    intro v hv
    change ‖v.1 • f (Complex.polarCoord.symm v)‖ₑ = _
    have hpos : 0<v.1 := hv.1
    simp [←ofReal_norm,norm_smul,abs_of_pos hpos,smul_eq_mul,ENNReal.ofReal_mul hpos.le]
  unfold area
  rw [Measure.restrict_smul,integral_smul_measure,ENNReal.toReal_ofReal (by positivity),←integral_indicator Metric.isOpen_ball.measurableSet]
  change (1/π:ℝ) • (∫ w, f w)=_
  rw [←Complex.integral_comp_polarCoord_symm]
  change (1/π:ℝ) • (∫ u in Ω, p u)=_
  unfold Ω at hp ⊢
  rw [polarCoord_target,Measure.volume_eq_prod,setIntegral_prod p hp]
  have eqn : ∀ᵐ r ∂volume.restrict (Ioi (0:ℝ)),
      (∫ θ in Ioo (-π) π, p (r,θ)) = (Ioo 0 ‖h‖).indicator (fun r : ℝ => (r:ℂ)*(((2*π:ℝ):ℂ)*h⁻¹)) r := by
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi,(volume.restrict (Ioi (0:ℝ))).ae_ne ‖h‖] with r hr0 hn
    have hrp : 0<r := hr0
    have hw (θ : ℝ) : ‖polarRay r θ‖=r := by rw [polarRay,norm_mul,Complex.norm_of_nonneg hrp.le,unitPhase_norm,mul_one]
    by_cases hs : r<R
    · have hball (θ : ℝ) : polarRay r θ∈ball (0:ℂ) R := by simpa only [mem_ball,dist_zero_right,hw] using hs
      simp only [p,polarRay_coord,f,indicator_of_mem (hball _),Complex.real_smul,integral_const_mul]
      rcases lt_or_gt_of_ne hn with hl | hl
      · rw [cauchy_circle_inner h hrp hl,indicator_of_mem (show r∈Ioo 0 ‖h‖ from ⟨hrp,hl⟩)]
      · rw [cauchy_circle_outer h hl,mul_zero,indicator_of_notMem (show r∉Ioo 0 ‖h‖ from fun hh => (not_lt_of_ge hl.le) hh.2)]
    · have hout (θ : ℝ) : polarRay r θ∉ball (0:ℂ) R := by simpa only [mem_ball,dist_zero_right,hw] using hs
      simp only [p,polarRay_coord,f,indicator_of_notMem (hout _),smul_zero,integral_zero]
      rw [indicator_of_notMem (show r∉Ioo 0 ‖h‖ from fun hh => hs (hh.2.trans hr))]
  rw [integral_congr_ae eqn,setIntegral_indicator measurableSet_Ioo,inter_eq_right.mpr Ioo_subset_Ioi_self,
    integral_mul_const,integral_complex_ofReal,←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le (norm_nonneg h),integral_id,
    Complex.real_smul]
  by_cases hn : h=0
  · simp [hn]
  · push_cast; simp only [zero_pow (by decide : 2 ≠ 0),sub_zero]
    rw [←Complex.mul_conj']
    field_simp [hn,Complex.ofReal_ne_zero.mpr pi_ne_zero] <;> ring

theorem disc_cauchy_transform {x z : ℂ} {R : ℝ} (hx : x∈ball z R) :
    (∫ w in ball z R, (x-w)⁻¹ ∂area)=conj (x-z) := by
  let e := Homeomorph.addRight z
  have hp := measurePreserving_add_right (volume:Measure ℂ) z
  have ha : MeasurePreserving (fun w : ℂ => w+z) area area := ⟨hp.measurable,by
    unfold area; rw [Measure.map_smul _ hp.measurable.aemeasurable,hp.map_eq]⟩
  have h := ha.setIntegral_preimage_emb e.measurableEmbedding (fun w => (x-w)⁻¹) (ball z R)
  have hpre : (fun w : ℂ => w+z) ⁻¹' ball z R=ball (0:ℂ) R := by ext w; simp [mem_ball,dist_eq_norm]
  rw [hpre] at h
  rw [←h]
  have he (w : ℂ) : x-(w+z)=x-z-w := by ring
  change (∫ w in ball (0:ℂ) R, (x-(w+z))⁻¹ ∂area)=_
  simp_rw [he]
  have hh : ‖x-z‖<R := by simpa [mem_ball,dist_eq_norm] using hx
  exact origin_disc_cauchy ((norm_nonneg _).trans_lt hh) hh

end Liu
