import Liu.GreenKernel

noncomputable section
open Set MeasureTheory
open scoped ComplexConjugate
namespace Liu

theorem greenLog_ratio_squared (z w : ℂ) (hz : 0 ≤ z.im) (hw : 0 < w.im) (hne : z ≠ w) :
    greenLog z w = (1/2:ℝ) * Real.log (1 + 4*z.im*w.im/‖z-w‖^2) := by
  have hconj : z ≠ conj w := fun he => by
    have hh := congrArg Complex.im he; simp at hh; linarith
  have hD := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
  have hN := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hconj))
  have sqdiff : ‖z-conj w‖^2 = ‖z-w‖^2 + 4*z.im*w.im := by
    simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.conj_re,Complex.conj_im]
    ring
  have hratio : 1+4*z.im*w.im/‖z-w‖^2 = ‖z-conj w‖^2/‖z-w‖^2 := by
    rw [sqdiff]; field_simp [norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)]
  rw [hratio,Real.log_div hN.ne' hD.ne',Real.log_pow,Real.log_pow]
  unfold greenLog
  rw [Real.log_div (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hconj))
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne))]
  ring

theorem greenLog_nonneg_le (z w : ℂ) (hz : 0 ≤ z.im) (hw : 0 < w.im) (hne : z ≠ w) :
    0 ≤ greenLog z w ∧ greenLog z w ≤ 2*z.im*w.im/‖z-w‖^2 := by
  rw [greenLog_ratio_squared z w hz hw hne]
  have hn : 0 ≤ 4*z.im*w.im/‖z-w‖^2 := by positivity
  have hl := Real.log_nonneg (show 1 ≤ 1+4*z.im*w.im/‖z-w‖^2 by linarith)
  have hu := Real.log_le_sub_one_of_pos (show 0 < 1+4*z.im*w.im/‖z-w‖^2 by linarith)
  constructor
  · positivity
  · calc
      _ ≤ (1/2:ℝ)*(4*z.im*w.im/‖z-w‖^2) := by linarith
      _ = _ := by ring

/-- Spatial derivative of the normalized moving half-plane Green kernel with respect to the
boundary height, at fixed interior evaluation and source points. Its scalar form is the first
equality in Appendix D's domain-variation computation. -/
theorem moving_green_derivative (x X y Y t : ℝ) (hy : t < y) (hY : t < Y)
    (hsep : 0 < (x-X)^2+(y-Y)^2) :
    HasDerivAt (fun T : ℝ => greenAtHeight x X (Y-T) (y-T) / 2)
      (-(y+Y-2*t)/((x-X)^2+(y+Y-2*t)^2)) t := by
  let K := (x-X)^2
  have hpos : 0 < K+(y+Y-2*t)^2 := by
    have hv : 0 < y+Y-2*t := by linarith
    dsimp [K]; positivity
  have dm := (((hasDerivAt_const t (y+Y)).sub ((hasDerivAt_id t).const_mul 2)).pow 2).const_add K
  have d := (((dm.log (by simpa using hpos.ne')).sub_const (Real.log (K+(y-Y)^2))).div_const 2).div_const 2
  convert d using 1
  · funext T
    dsimp [greenAtHeight,K]
    congr 3 <;> ring
  · dsimp [K]
    field_simp
    ring

/-- Local planar integrability of the reflected-potential gradient majorant near a source.
In two real dimensions the radial factor cancels the 1/r singularity. -/
theorem integrable_inverse_distance_ball (R : ℝ) :
    IntegrableOn (fun z : ℂ => ‖z‖⁻¹) (Metric.ball 0 R) volume := by
  apply integrableOn_ball_of_norm_le_rpow (C := 1) (α := 1) (by simp) (by simp)
  · filter_upwards with z
    simp [Real.rpow_neg (norm_nonneg _)]
  · exact (by fun_prop : Measurable (fun z : ℂ => ‖z‖⁻¹)).aestronglyMeasurable

end Liu
