module

public import Liu.CauchyTransform
public import Liu.CauchyDisc

@[expose] public section

noncomputable section
open Set MeasureTheory Real Filter Metric
open scoped Topology ComplexConjugate
namespace Liu

theorem cauchyTransform_hasDerivAt_of_quotient {f : ℂ → ℂ} {z : ℂ} (hf : QuadraticDecay f)
    (hq : QuadraticDecay (fun w => f w/(z-w))) :
    HasDerivAt (cauchyTransform f) (-(cauchyTransform (fun w => f w/(z-w)) z)) z := by
  rw [hasDerivAt_iff_tendsto_slope]
  apply (((cauchyTransform_continuous hq).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).neg).congr'
  filter_upwards [self_mem_nhdsWithin (a:=z) (s:={z}ᶜ)] with x hx
  have hn : x-z≠0 := sub_ne_zero.mpr (show x≠z from hx)
  rw [slope_def_field, cauchyTransform,cauchyTransform,cauchyTransform,←integral_sub (cauchyTransform_integrable hf x)
    (cauchyTransform_integrable hf z),←integral_div,←integral_neg]
  apply integral_congr_ae
  filter_upwards [upperArea_ae_ne x,upperArea_ae_ne z] with w hwx hwz
  field_simp [hn,sub_ne_zero.mpr hwx.symm,sub_ne_zero.mpr hwz.symm] <;> ring

private theorem disc_indicator_decay (z : ℂ) {R : ℝ} (hR : 0<R) (v : ℂ) :
    QuadraticDecay ((ball z R).indicator (fun _ => v)) := by
  refine ⟨measurable_const.indicator isOpen_ball.measurableSet,‖v‖*(1+‖z‖+R)^2,by positivity,?_⟩
  intro w hw
  by_cases h : w∈ball z R
  · rw [indicator_of_mem h]
    have hi := norm_add_le (w-z) z
    rw [sub_add_cancel] at hi
    have hh : ‖w-z‖<R := by simpa only [mem_ball,dist_eq_norm] using h
    apply (le_div_iff₀ (by positivity)).mpr
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) 2) (norm_nonneg v)
  · rw [indicator_of_notMem h,norm_zero]; positivity

theorem QuadraticDecay.sub {f g : ℂ → ℂ} (hf : QuadraticDecay f) (hg : QuadraticDecay g) :
    QuadraticDecay (fun w => f w-g w) := by
  obtain ⟨A,hA,ha⟩ := hf.bound
  obtain ⟨B,hB,hb⟩ := hg.bound
  exact ⟨hf.measurable.sub hg.measurable,A+B,add_nonneg hA hB,fun z hz =>
    (norm_sub_le ..).trans ((add_le_add (ha z hz) (hb z hz)).trans_eq (add_div ..).symm)⟩

private theorem subtract_disc_quotient {f : ℂ → ℂ} {z : ℂ} (hf : QuadraticDecay f)
    {R L : ℝ} (hR : 0<R) (hL : 0≤L) (hlip : ∀ w ∈ ball z R, ‖f w-f z‖ ≤ L*‖w-z‖) :
    QuadraticDecay (fun w => (f w-(ball z R).indicator (fun _ => f z) w)/(z-w)) := by
  obtain ⟨K,hK,hbound⟩ := hf.bound
  have hm := (hf.sub (disc_indicator_decay z hR (f z))).measurable
  refine ⟨by fun_prop, L*(1+‖z‖+R)^2+K/R,by positivity,?_⟩
  intro w hw
  rw [norm_div]
  have hW : 0<1+‖w‖ := by positivity
  by_cases near : w∈ball z R
  · rw [indicator_of_mem near]
    have hwz : ‖w-z‖<R := by simpa only [mem_ball,dist_eq_norm] using near
    have ht := norm_add_le (w-z) z
    rw [sub_add_cancel] at ht
    have hlocal : ‖f w-f z‖/‖z-w‖ ≤ L := by
      by_cases he : w=z
      · simp [he,hL]
      · rw [norm_sub_rev z w]
        exact (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr he))).mpr (hlip w near)
    apply hlocal.trans
    apply (le_div_iff₀ (sq_pos_of_pos hW)).mpr
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hW.le (by linarith) 2) hL).trans (le_add_of_nonneg_right (by positivity))
  · rw [indicator_of_notMem near,sub_zero]
    have hd : R ≤ ‖z-w‖ := by simpa [mem_ball,dist_eq_norm,norm_sub_rev w z] using near
    apply (div_le_div₀ (by positivity : 0≤K/(1+‖w‖)^2) (hbound w hw) hR hd).trans
    calc
      _ = (K/R)/(1+‖w‖)^2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (sq_nonneg _)

theorem cauchyTransform_local_decomposition {f : ℂ → ℂ} (hf : QuadraticDecay f) {z : ℂ} (hz : z∈upper)
    (hd : DifferentiableAt ℝ f z) :
    DifferentiableAt ℂ (fun x => cauchyTransform f x-f z*conj (x-z)) z := by
  obtain ⟨L,hL0,hlip⟩ := hd.isBigO_sub.exists_pos
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (hlip.bound.and (upper_open.mem_nhds hz))
  let b := (ball z r).indicator (fun _ => f z)
  have hb : QuadraticDecay b := disc_indicator_decay z hr (f z)
  have hq := subtract_disc_quotient hf hr hL0.le (fun w hw => (hsub hw).1)
  have hD := cauchyTransform_hasDerivAt_of_quotient (hf.sub hb) hq
  apply hD.differentiableAt.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds z hr] with x hx
  change cauchyTransform f x-f z*conj (x-z)=cauchyTransform (fun w => f w-b w) x
  have hB : cauchyTransform b x = f z*conj (x-z) := by
    have he : (fun w => b w/(x-w)) = (ball z r).indicator (fun w => f z*(x-w)⁻¹) := by
      funext w
      by_cases hw : w∈ball z r <;> simp [b,hw,div_eq_mul_inv]
    rw [cauchyTransform,he,integral_indicator isOpen_ball.measurableSet,upperArea,Measure.restrict_restrict isOpen_ball.measurableSet,
      inter_eq_left.mpr (show ball z r⊆upper from fun w hw => (hsub hw).2),integral_const_mul,disc_cauchy_transform hx]
  rw [←hB]
  unfold cauchyTransform
  simp only [sub_div,integral_sub (cauchyTransform_integrable hf x) (cauchyTransform_integrable hb x)]

end Liu
