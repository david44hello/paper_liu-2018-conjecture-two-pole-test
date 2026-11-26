import Liu.PowerDecay
import Liu.Potential

noncomputable section
open Set MeasureTheory
open scoped ComplexConjugate
namespace Liu

/-- The antiholomorphic derivative in the coordinates z=x+iy. -/
def dbar (f : ℂ → ℂ) (z : ℂ) : ℂ :=
    ((fderiv ℝ f z) 1 + Complex.I*(fderiv ℝ f z) Complex.I)/2

private theorem logInput_formula (f : ℂ → ℂ) :
    logInput f = fun w => (1/2:ℂ)*(f w * Complex.log (f w*conj (f w))) := by
  funext w
  unfold logInput
  rw [Complex.mul_conj',←Complex.ofReal_pow,←Complex.ofReal_log (sq_nonneg _),Real.log_pow]
  push_cast
  ring

/-- At every nonzero holomorphic value the actual Wirtinger derivative agrees with the
source in Appendix B. This argument also covers negative real values of f. -/
theorem dbar_logInput {f : ℂ → ℂ} {z a : ℂ} (h : HasDerivAt f a z) (hn : f z ≠ 0) :
    dbar (logInput f) z = (1/2:ℂ) * (f z/conj (f z)) * conj a := by
  have hpos : f z*conj (f z) ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    rw [Complex.mul_conj',←Complex.ofReal_pow,Complex.ofReal_re]
    exact sq_pos_of_pos (norm_pos_iff.mpr hn)
  have df := h.complexToReal_fderiv
  have dc := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp z df
  have dw := df.mul dc
  have dl := (Complex.hasStrictFDerivAt_log_real hpos).hasFDerivAt.comp z dw
  have dd := (df.mul dl).const_mul (1/2:ℂ)
  simp only [Function.comp_def,Pi.mul_apply,ContinuousLinearEquiv.coe_coe,Complex.conjCLE_apply] at dd
  rw [dbar,logInput_formula,dd.fderiv]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.one_apply,smul_eq_mul,
    Function.comp_apply,ContinuousLinearEquiv.coe_coe,Complex.conjCLE_apply,
    mul_one,map_mul,Complex.conj_I,Complex.I_mul_I]
  have hnc : conj (f z) ≠ 0 := by simpa using hn
  field_simp [hn,hnc]
  ring_nf
  <;> simp [Complex.I_sq]
  <;> ring

theorem PickSum.power_hasDerivAt {n : ℕ} (p : PickSum n) (ε : ℝ) {z : ℂ} (hz : 0 ≤ z.im) :
    HasDerivAt (p.power (1+ε)) (((1+ε:ℝ):ℂ)*p.power ε z*deriv p.value z) z := by
  have h := (p.hasDerivAt hz).differentiableAt.hasDerivAt.cpow_const (c := ((1+ε:ℝ):ℂ))
    (Complex.mem_slitPlane_iff.mpr (Or.inr (p.value_im_pos hz).ne'))
  unfold PickSum.power
  simpa using h

theorem PickSum.power_dbar_norm {n : ℕ} (p : PickSum n) {ε : ℝ} (he : 0 ≤ ε) {z : ℂ}
    (hz : 0 ≤ z.im) :
    ‖dbar (logInput (p.power (1+ε))) z‖ =
      (1+ε)*‖p.value z‖^ε*‖source p.value z‖ := by
  have hn := p.power_nonzero (1+ε) hz
  have hv : p.value z ≠ 0 := fun heq => by have hh := p.value_im_pos hz; simp [heq] at hh
  rw [dbar_logInput (p.power_hasDerivAt ε hz) hn,source_norm hv]
  simp only [norm_mul,norm_div,Complex.norm_conj,div_self (norm_ne_zero_iff.mpr hn),mul_one,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ 1+ε),PickSum.power,
    Complex.norm_cpow_real]
  have hnexp := (Real.rpow_pos_of_pos (norm_pos_iff.mpr hv) (1+ε)).ne'
  norm_num [hnexp]
  <;> ring

theorem PickSum.power_dbar_decay {n : ℕ} (p : PickSum n) {ε : ℝ} (he : 0 ≤ ε) {z : ℂ}
    (hz : 0 ≤ z.im) :
    ‖dbar (logInput (p.power (1+ε))) z‖ ≤
      ((1+ε)*p.bound^ε*(p.derivativeBound/2))/(1+‖z‖)^(2+ε:ℝ) := by
  rw [p.power_dbar_norm he hz]
  have h := Real.rpow_le_rpow (norm_nonneg _) (p.global_decay hz) he
  rw [Real.div_rpow p.bound_pos.le (by positivity)] at h
  have hb := p.bound_pos
  have hd : 0 < 1+‖z‖ := by positivity
  calc
    _ ≤ ((1+ε)*(p.bound^ε/(1+‖z‖)^ε))*((p.derivativeBound/2)/(1+‖z‖)^2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left h (by linarith)) (p.source_decay hz) (norm_nonneg _) (by positivity)
    _ = _ := by rw [Real.rpow_add hd,Real.rpow_ofNat]; field_simp [hd.ne',(Real.rpow_pos_of_pos hd ε).ne'] <;> ring

end Liu
