import Liu.SingleTrace
import Liu.SingleFluxConstant

noncomputable section
open Set MeasureTheory Real
namespace Liu

private theorem single_weight_integrable {b : ℝ} (hb : 0<b) (a x : ℝ) :
    IntegrableOn (fun t => poissonLine a t x/(t+b)) (Ioi b) := by
  have h := integrableOn_Ioi_rpow_of_lt (a:=(-2:ℝ)) (by norm_num) hb
  apply h.mono'
  · exact (show Measurable (fun t => poissonLine a t x/(t+b)) by unfold poissonLine; fun_prop).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioi (a:=b))] with t ht
  have ht0 := hb.trans ht
  have h1 : 0 < (x-a)^2+t^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos ht0)
  have h2 : 0 < t+b := add_pos ht0 hb
  simp only [poissonLine,Real.norm_eq_abs,abs_of_nonneg (div_nonneg (div_nonneg ht0.le h1.le) h2.le),
    rpow_neg ht0.le,rpow_ofNat]
  rw [div_div,←one_div,div_le_div_iff₀ (mul_pos h1 h2) (sq_pos_of_pos ht0)]
  nlinarith [mul_nonneg (sq_nonneg (x-a)) h2.le,mul_nonneg (sq_nonneg t) hb.le]

/-- Exact L² energy in dx/π of the positive boundary trace of a unit pole. -/
theorem isolatedTrace_energy (a : ℝ) {b : ℝ} (hb : 0 < b) :
    (∫ x, (isolatedTrace a b x)^2)/π = k₀/b := by
  let μ := (volume:Measure ℝ).restrict (Ioi b)
  let H := fun t x : ℝ => poissonLine a t x/(t+b)
  let K := fun z : ℝ × ℝ => ((z.1+b)*(z.2+b)*(z.1+z.2))⁻¹
  let G := fun (z : ℝ × ℝ) (x : ℝ) => H z.1 x*H z.2 x
  have good : ∀ᵐ z ∂μ.prod μ, b<z.1 ∧ b<z.2 ∧ z.1≠z.2 := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability : MeasurableSet {z : ℝ × ℝ | b<z.1 ∧ b<z.2 ∧ z.1≠z.2})).mpr
    filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioi (a:=b))] with t ht
    filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioi (a:=b)),μ.ae_ne t] with s hs hne
    exact ⟨ht,hs,hne.symm⟩
  have posK (t s : ℝ) (ht : b<t) (hs : b<s) : 0<K (t,s) := by
    have ht0 := hb.trans ht; have hs0 := hb.trans hs
    dsimp [K]; positivity
  have integKs (t : ℝ) (ht : b<t) : Integrable (fun s => K (t,s)) μ := by
    have ht0 := hb.trans ht
    have h := (integrableOn_Ioi_rpow_of_lt (a:=(-2:ℝ)) (by norm_num) hb).const_mul (t+b)⁻¹
    apply h.mono'
    · exact (show Measurable (fun s => K (t,s)) by dsimp [K]; fun_prop).aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioi (a:=b))] with s hs
    have hs0 := hb.trans hs
    rw [Real.norm_eq_abs,abs_of_pos (posK t s ht hs)]
    simp only [K,rpow_neg hs0.le,rpow_ofNat,mul_inv_rev]
    have he : s^2 ≤ (s+b)*(t+s) := by nlinarith [mul_nonneg ht0.le hs0.le,mul_nonneg hb.le (add_pos ht0 hs0).le]
    have hh := inv_anti₀ (sq_pos_of_pos hs0) he
    rw [mul_inv_rev] at hh
    nlinarith [mul_le_mul_of_nonneg_right hh (inv_nonneg.mpr (add_pos ht0 hb).le)]
  have hKv : (∫ t, ∫ s, K (t,s) ∂μ ∂μ) = k₀/b := single_trace_double_integral hb
  have hK : Integrable K (μ.prod μ) := by
    apply (integrable_prod_iff (show Measurable K by dsimp [K]; fun_prop).aestronglyMeasurable).mpr
    refine ⟨(ae_restrict_mem measurableSet_Ioi).mono (fun t ht => integKs t ht),?_⟩
    have ho : Integrable (fun t => ∫ s, K (t,s) ∂μ) μ := Integrable.of_integral_ne_zero
      (hKv ▸ (by unfold k₀; positivity))
    apply ho.congr
    filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioi (a:=b))] with t ht
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioi (a:=b))] with s hs
    exact (Real.norm_of_nonneg (posK t s ht hs).le).symm
  have hGval (t s : ℝ) (ht : b<t) (hs : b<s) (hne : t≠s) :
      (∫ x, G (t,s) x) = π*K (t,s) := by
    have hv := poissonLine_pair a a (hb.trans ht) (hb.trans hs) hne
    have he (x : ℝ) : G (t,s) x = (poissonLine a t x*poissonLine a s x)/((t+b)*(s+b)) := by
      dsimp [G,H]; rw [div_mul_div_comm]
    simp_rw [he,integral_div,hv]
    dsimp [K]
    field_simp [show t+s ≠ 0 by linarith,show t+b≠0 by linarith,show s+b≠0 by linarith] <;> ring
  have hG : Integrable (Function.uncurry G) ((μ.prod μ).prod volume) := by
    have hm : Measurable (Function.uncurry G) := by dsimp [Function.uncurry,G,H,poissonLine]; fun_prop
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    constructor
    · filter_upwards [good] with z hz
      apply Integrable.of_integral_ne_zero
      change (∫ x, G (z.1,z.2) x) ≠ 0
      rw [hGval _ _ hz.1 hz.2.1 hz.2.2]
      exact (mul_pos pi_pos (posK _ _ hz.1 hz.2.1)).ne'
    · apply (hK.const_mul π).congr
      filter_upwards [good] with z hz
      rw [←hGval _ _ hz.1 hz.2.1 hz.2.2]
      apply integral_congr_ae
      filter_upwards with x
      have ht := hb.trans hz.1; have hs := hb.trans hz.2.1
      exact (Real.norm_of_nonneg (show 0 ≤ G z x by dsimp [G,H,poissonLine]; positivity)).symm
  have he (x : ℝ) : (isolatedTrace a b x)^2 = ∫ z, G z x ∂μ.prod μ := by
    rw [show (∫ z, G z x ∂μ.prod μ) = (∫ t, H t x ∂μ)*(∫ s, H s x ∂μ) from integral_prod_mul (μ:=μ) (ν:=μ) (fun t => H t x) (fun t => H t x)]
    rw [pow_two]; rfl
  simp_rw [he]
  rw [←integral_integral_swap hG]
  have hh : (∫ z, ∫ x, G z x ∂volume ∂μ.prod μ) = ∫ z, π*K z ∂μ.prod μ := by
    apply integral_congr_ae
    filter_upwards [good] with z hz
    exact hGval _ _ hz.1 hz.2.1 hz.2.2
  rw [hh,integral_const_mul,integral_prod K hK,hKv,mul_div_cancel_left₀ _ pi_ne_zero]

end Liu
