module

public import Liu.Comparability

@[expose] public section

noncomputable section
open Filter Real MeasureTheory Set
open scoped Topology ComplexConjugate
namespace Liu

def linePole (a b x : ℝ) : ℂ := ((x-a:ℝ)+((b:ℂ)*Complex.I))⁻¹

private def linePrimitive (a b x : ℝ) : ℂ :=
  ((Real.log ((x-a)^2+b^2)/2:ℝ):ℂ) - (arctan ((x-a)/b):ℂ)*Complex.I

private theorem linePole_ne {b : ℝ} (hb : 0 < b) (a x : ℝ) :
    ((x-a:ℝ):ℂ)+(b:ℂ)*Complex.I ≠ 0 := by
  intro h
  have hh := congrArg Complex.im h
  simp at hh
  linarith

theorem linePole_continuous (a : ℝ) {b : ℝ} (hb : 0 < b) : Continuous (linePole a b) := by
  unfold linePole
  exact Continuous.inv₀ (by fun_prop) (linePole_ne hb a)

private theorem linePrimitive_deriv (a : ℝ) {b : ℝ} (hb : 0 < b) (x : ℝ) :
    HasDerivAt (linePrimitive a b) (linePole a b x) x := by
  have d := (hasDerivAt_id x).sub_const a
  have hp : 0 < (x-a)^2+b^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hb)
  have dr : HasDerivAt (fun y : ℝ => log ((y-a)^2+b^2)/2) ((x-a)/((x-a)^2+b^2)) x := by
    convert (((d.pow 2).add_const (b^2)).log (by simpa using hp.ne')).div_const 2 using 1
    · rfl
    change (x-a)/((x-a)^2+b^2) = (2*(x-a)^(2-1:ℕ)*1/((x-a)^2+b^2))/2
    norm_num; ring
  have di : HasDerivAt (fun y : ℝ => arctan ((y-a)/b)) (b/((x-a)^2+b^2)) x := by
    convert (d.div_const b).arctan using 1
    · rfl
    change b/((x-a)^2+b^2) = (1/(1+((x-a)/b)^2))*(1/b)
    field_simp [hb.ne',hp.ne']
    <;> ring
  convert dr.ofReal_comp.sub (di.ofReal_comp.mul_const Complex.I) using 1
  · rfl
  · unfold linePole
    apply Complex.ext <;> simp only [Complex.inv_re,Complex.inv_im,Complex.normSq_apply,
      Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.mul_I_re,Complex.mul_I_im,zero_add,add_zero,sub_zero,neg_zero,zero_sub]
    all_goals rw [←sq (x-a),←sq b] <;> simp [div_eq_mul_inv]

private theorem symmetric_log_ratio (a b : ℝ) (hb : 0 < b) :
    Tendsto (fun R : ℝ => Real.log ((R-a)^2+b^2) - Real.log ((-R-a)^2+b^2)) atTop (𝓝 0) := by
  have hr : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hrat : Tendsto (fun R : ℝ => ((1-a*R⁻¹)^2+(b*R⁻¹)^2)/
      ((-1-a*R⁻¹)^2+(b*R⁻¹)^2)) atTop (𝓝 1) := by
    have h := (show Tendsto (fun R : ℝ => (1-a*R⁻¹)^2+(b*R⁻¹)^2) atTop (𝓝 ((1-a*0)^2+(b*0)^2)) from
      ((tendsto_const_nhds.sub (hr.const_mul a)).pow 2).add ((hr.const_mul b).pow 2))
    have h' := (show Tendsto (fun R : ℝ => (-1-a*R⁻¹)^2+(b*R⁻¹)^2) atTop (𝓝 ((-1-a*0)^2+(b*0)^2)) from
      ((tendsto_const_nhds.sub (hr.const_mul a)).pow 2).add ((hr.const_mul b).pow 2))
    simpa [Pi.div_def] using h.div h' (by norm_num)
  have hg := (Real.continuousAt_log (by norm_num : (1:ℝ) ≠ 0)).tendsto.comp hrat
  rw [Real.log_one] at hg
  apply hg.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
  have h₁ : 0 < (R-a)^2+b^2 := by positivity
  have h₂ : 0 < (-R-a)^2+b^2 := by positivity
  rw [←Real.log_div h₁.ne' h₂.ne']
  change Real.log _ = Real.log _
  congr 1
  have hf (u : ℝ) : (u-a*R⁻¹)^2+(b*R⁻¹)^2 = ((u*R-a)^2+b^2)/R^2 := by
    field_simp [hR.ne'] <;> ring
  simp only [hf,one_mul,neg_one_mul,div_div_div_cancel_right₀ (pow_ne_zero 2 hR.ne')]

/-- Symmetric real-line integral of a single resolvent whose pole is below the axis. -/
theorem linePole_principal_value (a : ℝ) {b : ℝ} (hb : 0<b) :
    Tendsto (fun R : ℝ => ∫ x in -R..R, linePole a b x) atTop (𝓝 (-(Real.pi:ℂ)*Complex.I)) := by
  have hreal := (symmetric_log_ratio a b hb).div_const 2
  have ht : Tendsto (fun R : ℝ => (R-a)/b) atTop atTop := by
    simpa [sub_eq_add_neg,div_eq_mul_inv] using
      (tendsto_atTop_add_const_right atTop (-a) tendsto_id).atTop_mul_const (inv_pos.mpr hb)
  have ht' : Tendsto (fun R : ℝ => (-R-a)/b) atTop atBot := by
    have h := (tendsto_atTop_add_const_right atTop a tendsto_id).atTop_mul_const (inv_pos.mpr hb)
    convert tendsto_neg_atTop_atBot.comp h using 1
    funext R; simp [Function.comp_def,id,div_eq_mul_inv]; ring
  have ha := (tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp ht
  have hb' := (tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp ht'
  have hsum := (Complex.continuous_ofReal.continuousAt.tendsto.comp hreal).sub
    ((Complex.continuous_ofReal.continuousAt.tendsto.comp (ha.sub hb')).mul_const Complex.I)
  convert hsum using 1
  · funext R
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => linePrimitive_deriv a hb x)
      ((linePole_continuous a hb).intervalIntegrable ..)]
    simp [linePrimitive,Function.comp_apply]
    ring
  · congr 1
    push_cast
    ring

end Liu
