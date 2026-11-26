import Liu.PickSums

noncomputable section
open MeasureTheory Set
namespace Liu

/-- A positive power absorbs the logarithmic weight, uniformly for 0<x≤C. -/
theorem weighted_log_constant {C q : ℝ} (hC : 1 ≤ C) (hq : 0 < q) :
    ∃ M > 0, ∀ x : ℝ, 0 < x → x ≤ C → x^q * (1+|Real.log x|) ≤ M := by
  let M := 1 + 1/q + C^q*(1+Real.log C)
  have cp : 0 < C := by linarith
  have lgC := Real.log_nonneg hC
  have high : 0 ≤ C^q*(1+Real.log C) := by positivity
  refine ⟨M,by dsimp [M]; positivity,?_⟩
  intro x hx hxc
  by_cases low : x ≤ 1
  · have h₁ := Real.rpow_le_one hx.le low hq.le
    have h₂ := (Real.abs_log_mul_self_rpow_lt x q hx low hq).le
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hx.le _)] at h₂
    dsimp [M]
    nlinarith
  · have hl := Real.log_nonneg (le_of_not_ge low)
    rw [abs_of_nonneg hl]
    have hcomp : x^q * (1+Real.log x) ≤ C^q*(1+Real.log C) := by
      gcongr
    dsimp [M]
    linarith [one_div_pos.mpr hq]

theorem PickSum.norm_power_integrable {n : ℕ} (p : PickSum n) {r : ℝ} (hr : 2 < r) :
    Integrable (fun z => ‖p.value z‖^r) upperArea := by
  have hh : (Module.finrank ℝ ℂ : ℝ) < r := by simpa using hr
  have dom := integrable_one_add_norm (μ := (volume:Measure ℂ)) hh
  have dom' : Integrable (fun z : ℂ => p.bound^r * (1+‖z‖)^(-r)) upperArea :=
    (((dom.const_mul _).smul_measure ENNReal.ofReal_ne_top).restrict)
  apply dom'.mono'
  · have hm : Measurable p.value := by
      have h := p.power_measurable 1
      change Measurable (fun z => (p.value z)^((1:ℝ):ℂ)) at h
      simpa using h
    exact (hm.norm.pow_const r).aestronglyMeasurable
  · have hu : MeasurableSet upper := (isOpen_lt continuous_const Complex.continuous_im).measurableSet
    apply (ae_restrict_iff' hu).2
    filter_upwards with z hz
    have ht := p.global_decay (le_of_lt hz)
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    calc
      _ ≤ (p.bound/(1+‖z‖))^r := Real.rpow_le_rpow (norm_nonneg _) ht (by linarith)
      _ = _ := by rw [Real.div_rpow p.bound_pos.le (by positivity),Real.rpow_neg (by positivity : 0 ≤ 1+‖z‖),div_eq_mul_inv]

/-- The integrability half of the admissibility criterion, including its fifth log moment. -/
theorem PickSum.weighted_power_integrable {n : ℕ} (p : PickSum n) {t v : ℝ}
    (ht : 0 < t) (hv : 2 < t*v) :
    Integrable (fun z => ‖p.power t z‖^v * (1+|Real.log ‖p.power t z‖|)^5) upperArea := by
  let q := (t*v-2)/(10*t)
  have hq : 0 < q := by dsimp [q]; positivity
  have hrv : 2 < t*(v-5*q) := by
    dsimp [q]
    field_simp
    nlinarith [mul_pos ht (sub_pos.mpr hv)]
  let C := max 1 (p.bound^t)
  obtain ⟨M,hM,hbound⟩ := weighted_log_constant (C := C) (le_max_left ..) hq
  have dom := (p.norm_power_integrable hrv).const_mul (M^5)
  apply dom.mono'
  · have hmeas := p.power_measurable t
    fun_prop
  · apply (ae_restrict_iff' (show MeasurableSet upper from (isOpen_lt continuous_const Complex.continuous_im).measurableSet)).2
    filter_upwards with z hz
    let x := ‖p.power t z‖
    have nz : p.value z ≠ 0 := fun he => by
      have hi := p.value_im_pos (le_of_lt hz)
      simp [he] at hi
    have xid : x = ‖p.value z‖^t := Complex.norm_cpow_real _ _
    have hx : 0 < x := xid.symm ▸ Real.rpow_pos_of_pos (norm_pos_iff.mpr nz) _
    have hxC : x ≤ C := by
      rw [xid]
      apply le_trans _ (le_max_right 1 _)
      apply Real.rpow_le_rpow (norm_nonneg _) _ ht.le
      exact (p.global_decay (le_of_lt hz)).trans (div_le_self p.bound_pos.le (by linarith [norm_nonneg z]))
    have hlog := pow_le_pow_left₀ (show 0 ≤ x^q*(1+|Real.log x|) by positivity) (hbound x hx hxC) 5
    have factor : x^v = x^(v-5*q) * (x^q)^5 := by
      rw [← Real.rpow_natCast,←Real.rpow_mul hx.le,←Real.rpow_add hx]
      congr 1; push_cast; ring
    have scale : x^(v-5*q) = ‖p.value z‖^(t*(v-5*q)) := by rw [xid,Real.rpow_mul (norm_nonneg _)]
    change ‖x^v * (1+|Real.log x|)^5‖ ≤ M^5*‖p.value z‖^(t*(v-5*q))
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),factor,←scale]
    calc
      _ = x^(v-5*q)*(x^q*(1+|Real.log x|))^5 := by ring
      _ ≤ _ := by rw [mul_comm (M^5)]; gcongr

theorem PickSum.integrability_window {n : ℕ} (p : PickSum n) {ε η v : ℝ}
    (he : 0 < ε) (hη : η < 2*ε/(1+ε)) (hv : |v-2| ≤ η) :
    Integrable (fun z => ‖p.power (1+ε) z‖^v * (1+|Real.log ‖p.power (1+ε) z‖|)^5) upperArea := by
  have hp : 0 < 1+ε := by linarith
  have hh := (lt_div_iff₀ hp).mp hη
  apply p.weighted_power_integrable hp
  have hl := (abs_le.mp hv).1
  nlinarith [mul_le_mul_of_nonneg_left hl hp.le]

end Liu
