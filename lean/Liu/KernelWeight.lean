module

public import Liu.Dilation
public import Liu.Reproducing

@[expose] public section

noncomputable section
open Set MeasureTheory Metric Real
namespace Liu

def radialWeight (t : ℝ) (v : ℂ) := ‖v‖^(-t)/(1+‖v‖)

theorem radialWeight_integrable {t : ℝ} (ht : 1<t) (ht' : t<2) : Integrable (radialWeight t) volume := by
  have h0 : 0<t := by linarith
  have hm : Measurable (radialWeight t) := by unfold radialWeight; fun_prop
  have hl : IntegrableOn (radialWeight t) (ball (0:ℂ) 1) volume := by
    apply integrableOn_ball_of_norm_le_rpow (C:=1) (α:=t) (by simp) (by simpa using ht')
    · filter_upwards with v
      rw [Real.norm_eq_abs,abs_of_nonneg (by unfold radialWeight; positivity),one_mul]
      exact div_le_self (rpow_nonneg (norm_nonneg _) _) (by linarith [norm_nonneg v])
    · exact hm.aestronglyMeasurable
  have hd := integrable_one_add_norm (μ:=(volume:Measure ℂ)) (r:=1+t) (by simp; linarith)
  have hfar : IntegrableOn (radialWeight t) (ball (0:ℂ) 1)ᶜ volume := by
    apply (hd.const_mul ((2:ℝ)^t)).restrict.mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ:=volume) Metric.isOpen_ball.measurableSet.compl] with v hv
    have hr : 1 ≤ ‖v‖ := by simpa using hv
    have hrp : 0 < ‖v‖ := zero_lt_one.trans_le hr
    have hR : 0 < 1+‖v‖ := by positivity
    have hp := rpow_le_rpow hR.le (show 1+‖v‖ ≤ 2*‖v‖ by linarith) h0.le
    rw [mul_rpow (by norm_num) hrp.le] at hp
    rw [Real.norm_eq_abs,abs_of_nonneg (by unfold radialWeight; positivity)]
    simp only [radialWeight,rpow_neg hrp.le,rpow_neg hR.le,rpow_add hR,rpow_one]
    field_simp [hrp.ne',hR.ne',(rpow_pos_of_pos hrp t).ne',(rpow_pos_of_pos hR t).ne']
    <;> nlinarith [mul_le_mul_of_nonneg_left hp hR.le]
  simpa [←integrableOn_univ] using hl.union hfar

theorem scaled_localInverse_integral (z : ℂ) (r : ℝ) (hr : 0<r) :
    (∫ w, localInverse z ((r:ℝ) • w)) =
      (r^2)⁻¹*(∫ w, localInverse 0 w) := by
  rw [Measure.integral_comp_smul_of_nonneg volume _ r (hR:=hr.le),Complex.finrank_real_complex,
    smul_eq_mul,localInverse_integral]

end Liu
