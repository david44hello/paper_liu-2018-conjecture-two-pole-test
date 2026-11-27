module

public import Liu.EdgeTraceL1

@[expose] public section

noncomputable section
open Set Real MeasureTheory
namespace Liu

private def poissonWeight (u x : ℝ) (p : ℝ×ℝ) : ENNReal := ‖(1/π)*poissonLine x (p.1-u) p.2‖ₑ

private def poissonMeasure (u x : ℝ) : Measure (ℝ×ℝ) :=
  (((volume:Measure ℝ).restrict (Ioi u)).prod volume).withDensity (poissonWeight u x)

private theorem magnitude_is_integral (u x : ℝ) {f : ℂ → ℝ} (hf : Measurable f) :
    poissonMagnitude u x f = ∫⁻ p, ‖f ⟨p.2,p.1⟩‖ₑ ∂poissonMeasure u x := by
  have hmk : Measurable (fun p : ℝ×ℝ => (⟨p.2,p.1⟩:ℂ)) :=
    Complex.measurableEquivRealProd.symm.measurable.comp measurable_swap
  have hP : Measurable (poissonWeight u x) := by unfold poissonWeight poissonLine; fun_prop
  have hF : Measurable (fun p : ℝ×ℝ => ‖f ⟨p.2,p.1⟩‖ₑ) := (hf.comp hmk).enorm
  rw [poissonMeasure,lintegral_withDensity_eq_lintegral_mul _ hP hF,
    lintegral_prod _ (hP.mul hF).aemeasurable]
  unfold poissonMagnitude
  simp only [Pi.mul_apply,poissonWeight,enorm_mul,mul_assoc]
  simp_rw [lintegral_const_mul' _ _ (enorm_ne_top (x:=(1:ℝ)/π))]

private theorem magnitude_height (u x : ℝ) {W : ℝ → ℝ} (hW : Measurable W) :
    poissonMagnitude u x (fun z => W z.im) = ∫⁻ Y in Ioi u, ‖W Y‖ₑ := by
  have hm (Y : ℝ) (hY : u<Y) : (∫⁻ X, ‖poissonLine x (Y-u) X‖ₑ) = ‖π‖ₑ := by
    have h := sub_pos.mpr hY
    have hi : Integrable (poissonLine x (Y-u)) := Integrable.of_integral_ne_zero ((poissonLine_integral x h) ▸ pi_ne_zero)
    rw [←ofReal_integral_norm_eq_lintegral_enorm hi]
    have hh (X : ℝ) : ‖poissonLine x (Y-u) X‖=poissonLine x (Y-u) X := Real.norm_of_nonneg (by unfold poissonLine; positivity)
    simp_rw [hh,poissonLine_integral x h,Real.enorm_eq_ofReal pi_pos.le]
  unfold poissonMagnitude
  simp_rw [enorm_mul,lintegral_mul_const' _ _ (enorm_ne_top (x:=W _))]
  rw [←lintegral_const_mul' _ _ (enorm_ne_top (x:=(1:ℝ)/π))]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioi (a:=u))] with Y hY
  rw [hm Y hY,←mul_assoc,←enorm_mul,one_div_mul_cancel pi_ne_zero,enorm_one,one_mul]

private theorem integral_cauchy_sq {α : Type*} [MeasurableSpace α] (ν : Measure α)
    {g h : α → ℝ} (hg : Measurable g) (hh : Measurable h) :
    (∫⁻ p, ‖g p*h p‖ₑ ∂ν)^2 ≤ (∫⁻ p, ‖g p^2‖ₑ ∂ν)*(∫⁻ p, ‖h p^2‖ₑ ∂ν) := by
  have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two hg.enorm.aemeasurable hh.enorm.aemeasurable
  have hs := pow_le_pow_left' hcs 2
  simp only [Pi.mul_apply,ENNReal.rpow_ofNat,mul_pow,one_div] at hs
  have hroot (t : ENNReal) : (t^((2:ℝ)⁻¹))^2=t := ENNReal.rpow_inv_natCast_pow (n:=2) (by decide) t
  simpa only [enorm_mul,enorm_pow,hroot] using hs

/-- Weighted Cauchy–Schwarz in the positive Poisson measure. W depends only
on height, so its square integrates independently of the boundary point. -/
theorem depthPoissonReal_weighted_sq (u x : ℝ) {W : ℝ → ℝ} (hW : Measurable W)
    {g : ℂ → ℝ} (hg : Measurable g) :
    ‖depthPoissonReal u x (fun z => W z.im*g z)‖ₑ^2 ≤
      (∫⁻ Y in Ioi u, ‖W Y^2‖ₑ)*poissonMagnitude u x (fun z => g z^2) := by
  have hmk : Measurable (fun p : ℝ×ℝ => (⟨p.2,p.1⟩:ℂ)) :=
    Complex.measurableEquivRealProd.symm.measurable.comp measurable_swap
  have hWz := hW.comp Complex.measurable_im
  apply (pow_le_pow_left' (depthPoissonReal_enorm_le u x _) 2).trans
  rw [magnitude_is_integral _ _ (f:=fun z => W z.im*g z) (hWz.mul hg),←magnitude_height u x (W:=fun Y => W Y^2) (hW.pow_const 2),
    magnitude_is_integral _ _ (f:=fun z => W z.im^2) (hWz.pow_const 2),magnitude_is_integral _ _ (f:=fun z => g z^2) (hg.pow_const 2)]
  exact integral_cauchy_sq _ (hW.comp measurable_fst) (hg.comp hmk)

theorem depthPoissonReal_weighted_L2 {u : ℝ} (hu : 0≤u) {W : ℝ → ℝ} (hW : Measurable W)
    {g : ℂ → ℝ} (hg : Measurable g) {A : ℝ} (hA : 0≤A)
    (hweight : (∫⁻ Y in Ioi u, ‖W Y^2‖ₑ)≤ENNReal.ofReal A) :
    ENNReal.ofReal (1/π)*(∫⁻ x, ‖depthPoissonReal u x (fun z => W z.im*g z)‖ₑ^2) ≤
      ENNReal.ofReal A * ∫⁻ z, ‖g z^2‖ₑ ∂upperArea := by
  have hpt (x : ℝ) := (depthPoissonReal_weighted_sq u x hW hg).trans
    (mul_le_mul_of_nonneg_right hweight (zero_le (a:=poissonMagnitude u x (fun z => g z^2))))
  apply (mul_le_mul_of_nonneg_left (lintegral_mono hpt) zero_le).trans
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,mul_left_comm]
  exact mul_le_mul_of_nonneg_left (poissonMagnitude_lintegral (hg.pow_const 2) hu) zero_le

end Liu
