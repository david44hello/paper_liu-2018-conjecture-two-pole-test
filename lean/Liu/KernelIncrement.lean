module

public import Liu.GreenEstimates

@[expose] public section

noncomputable section
open Set Real MeasureTheory Metric
namespace Liu

/-- A fractional estimate of the increment of the planar Cauchy kernel.
The power 3/4 is sufficient for a squared energy increment of order o(h). -/
theorem cauchy_increment_bound {a b : ℂ} (ha : a≠0) (hb : b≠0) :
    ‖a⁻¹-b⁻¹‖ ≤ 2*‖a-b‖^(3/4:ℝ)*(‖a‖^(-(7/4:ℝ))+‖b‖^(-(7/4:ℝ))) := by
  let r := min ‖a‖ ‖b‖
  let h := ‖a-b‖
  have hra : 0<‖a‖ := norm_pos_iff.mpr ha
  have hrb : 0<‖b‖ := norm_pos_iff.mpr hb
  have hr : 0<r := lt_min hra hrb
  have hA : r≤‖a‖ := min_le_left .. 
  have hB : r≤‖b‖ := min_le_right .. 
  have hh : 0≤h := norm_nonneg _
  have hs : r^(-(7/4:ℝ))≤‖a‖^(-(7/4:ℝ))+‖b‖^(-(7/4:ℝ)) := by
    rcases le_total ‖a‖ ‖b‖ with h | h
    · dsimp only [r]; rw [min_eq_left h]; exact le_add_of_nonneg_right (by positivity)
    · dsimp only [r]; rw [min_eq_right h]; exact le_add_of_nonneg_left (by positivity)
  apply le_trans _ (mul_le_mul_of_nonneg_left hs (show 0≤2*h^(3/4:ℝ) by positivity))
  by_cases hhi : r≤h
  · have hnorm : ‖a⁻¹-b⁻¹‖≤2*r⁻¹ := by
      apply (norm_sub_le ..).trans
      rw [norm_inv,norm_inv]; linarith [inv_anti₀ hr hA,inv_anti₀ hr hB]
    apply hnorm.trans
    have he : r^(3/4:ℝ)*r^(-(7/4:ℝ))=r⁻¹ := by rw [←rpow_add hr,show (3/4:ℝ)+- (7/4)= -1 by norm_num,rpow_neg_one]
    have hp := mul_le_mul_of_nonneg_right (rpow_le_rpow hr.le hhi (by norm_num : 0≤(3/4:ℝ))) (rpow_nonneg hr.le (-(7/4:ℝ)))
    rw [he] at hp; linarith
  · have he : a⁻¹-b⁻¹=(b-a)/(a*b) := by field_simp [ha,hb]
    rw [he,norm_div,norm_mul,norm_sub_rev b a]
    have hden : r^2≤‖a‖*‖b‖ := by rw [sq]; exact mul_le_mul hA hB hr.le hra.le
    apply (div_le_div_of_nonneg_left hh (sq_pos_of_pos hr) hden).trans
    have hpow : h^(3/4:ℝ)*h^(1/4:ℝ)=h := by rw [←rpow_add_of_nonneg hh (by norm_num) (by norm_num)]; norm_num
    have hscale : r^(1/4:ℝ)/r^2=r^(-(7/4:ℝ)) := by rw [←Real.rpow_two,←Real.rpow_sub hr]; norm_num
    have hsmall := mul_le_mul_of_nonneg_left (rpow_le_rpow hh (le_of_not_ge hhi) (by norm_num : 0≤(1/4:ℝ))) (rpow_nonneg hh (3/4:ℝ))
    rw [hpow] at hsmall
    apply (div_le_div_of_nonneg_right hsmall (sq_nonneg r)).trans
    rw [mul_div_assoc,hscale]
    nlinarith only [mul_nonneg (rpow_nonneg hh (3/4:ℝ)) (rpow_nonneg hr.le (-(7/4:ℝ)))]

end Liu
