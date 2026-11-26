import Liu.SingleTrace

noncomputable section
open Set MeasureTheory Real
namespace Liu

theorem isolatedTrace_le_depth (a x : ℝ) {b : ℝ} (hb : 0 < b) : isolatedTrace a b x ≤ 1/b := by
  have hd := integrableOn_Ioi_rpow_of_lt (a:=(-2:ℝ)) (by norm_num) hb
  have hpos : 0 ≤ᵐ[(volume:Measure ℝ).restrict (Ioi b)] (fun t => poissonLine a t x/(t+b)) := by
    filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioi (a:=b))] with t ht
    have := hb.trans ht
    unfold poissonLine; positivity
  have he : (∫ t in Ioi b, t^(-(2:ℝ))) = 1/b := by
    rw [integral_Ioi_rpow_of_lt (by norm_num) hb]
    norm_num [Real.rpow_neg_one]
  rw [←he]
  apply integral_mono_of_nonneg hpos hd
  filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioi (a:=b))] with t ht
  have ht0 := hb.trans ht
  have hd1 : 0<(x-a)^2+t^2 := by positivity
  have hd2 := add_pos ht0 hb
  rw [poissonLine,div_div,rpow_neg ht0.le,rpow_ofNat,←one_div,div_le_div_iff₀ (mul_pos hd1 hd2) (sq_pos_of_pos ht0)]
  nlinarith [mul_nonneg (sq_nonneg (x-a)) hd2.le,mul_nonneg (sq_nonneg t) hb.le]

theorem isolatedTrace_le_distance (a x : ℝ) {b : ℝ} (hb : 0 < b) (hx : x ≠ a) :
    isolatedTrace a b x ≤ π/(2*|x-a|) := by
  let D := |x-a|
  have hD : 0<D := abs_pos.mpr (sub_ne_zero.mpr hx)
  let g := fun t : ℝ => (D^2+t^2)⁻¹
  have hshape (t : ℝ) : g t = (D^2)⁻¹ * (1+(D⁻¹*t)^2)⁻¹ := by
    dsimp [g]
    field_simp [hD.ne',show 1+(D⁻¹*t)^2 ≠ 0 by positivity,show D^2+t^2 ≠ 0 by positivity]
    <;> ring
  have hg : Integrable g := by
    simp_rw [show g = fun t : ℝ => (D^2)⁻¹ * (1+(D⁻¹*t)^2)⁻¹ from funext hshape]
    exact (integrable_inv_one_add_mul_sq (inv_ne_zero hD.ne')).const_mul _
  have hzero : (∫ t in Ioi (0:ℝ), g t) = π/(2*D) := by
    simp_rw [hshape,integral_const_mul]
    have h := integral_comp_mul_left_Ioi (fun x : ℝ => (1+x^2)⁻¹) 0 (b:=D⁻¹) (inv_pos.mpr hD)
    simp only [mul_zero,integral_Ioi_inv_one_add_sq,arctan_zero,sub_zero,inv_inv,smul_eq_mul] at h
    rw [h]; field_simp [hD.ne'] <;> ring
  have hinc : (∫ t in Ioi b, g t) ≤ ∫ t in Ioi (0:ℝ), g t :=
    setIntegral_mono_set hg.integrableOn (ae_of_all _ fun t => inv_nonneg.mpr (add_nonneg (sq_nonneg _) (sq_nonneg _)))
      (Filter.Eventually.of_forall (Ioi_subset_Ioi hb.le))
  apply le_trans _ (hinc.trans hzero.le)
  refine integral_mono_of_nonneg ?_ hg.integrableOn ?_
  · filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioi (a:=b))] with t ht
    have := hb.trans ht
    unfold poissonLine; positivity
  · filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioi (a:=b))] with t ht
    have ht0 := hb.trans ht
    have den := add_pos_of_nonneg_of_pos (sq_nonneg (x-a)) (sq_pos_of_pos ht0)
    change poissonLine a t x/(t+b) ≤ (|x-a|^2+t^2)⁻¹
    rw [poissonLine,sq_abs,div_div,←one_div,div_le_div_iff₀ (mul_pos den (add_pos ht0 hb)) den]
    nlinarith [mul_nonneg den.le hb.le]

end Liu
