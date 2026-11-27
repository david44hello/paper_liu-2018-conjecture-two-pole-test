module

public import Liu.SourceDefect

@[expose] public section

noncomputable section
open scoped ComplexConjugate
namespace Liu

/-- The normalized logarithmic derivative in Appendix B, with its actual mass. -/
theorem PickSum.reciprocalDerivative_error {n : ℕ} (p : PickSum n) :
    ∃ C > 0, ∀ z : ℂ, 0 ≤ z.im → ‖deriv p.value z/(p.value z)^2-(p.mass:ℂ)⁻¹‖ ≤
      C/(1+‖z‖)^2 := by
  obtain ⟨K,hK,hq⟩ := p.derivative_quartic_defect
  obtain ⟨c,hc,hl⟩ := p.two_sided_decay
  have hm := p.mass_pos
  refine ⟨K/(p.mass*c^2),by positivity,?_⟩
  intro z hz
  let R := 1+‖z‖
  have hR : 0<R := by dsimp [R]; positivity
  have hv : p.value z≠0 := fun he => by have hh := p.value_im_pos hz; simp [he] at hh
  have heq : deriv p.value z/(p.value z)^2-(p.mass:ℂ)⁻¹ =
      ((p.mass:ℂ)*deriv p.value z-(p.value z)^2)/((p.mass:ℂ)*(p.value z)^2) := by
    field_simp [hv,Complex.ofReal_ne_zero.mpr hm.ne']
  rw [heq,norm_div,norm_mul,norm_pow,Complex.norm_of_nonneg hm.le]
  have hlow := pow_le_pow_left₀ (show 0 ≤ c/R by positivity) (hl z hz).1 2
  have hp : 0 < p.mass*(c/R)^2 := by positivity
  calc
    _ ≤ (K/R^4)/(p.mass*(c/R)^2) := div_le_div₀ (by positivity) (hq z hz) hp
      (mul_le_mul_of_nonneg_left hlow hm.le)
    _ = _ := by change _ = _/R^2; field_simp [hR.ne',hc.ne',hm.ne'] <;> ring

theorem PickSum.logSource_realModel_error {n : ℕ} (p : PickSum n) :
    ∃ C > 0, ∀ z : ℂ, 0 ≤ z.im →
      ‖dbar (logInput p.value) z - ((‖p.value z‖^2/(2*p.mass):ℝ):ℂ)‖ ≤ C/(1+‖z‖)^4 := by
  obtain ⟨K,hK,hq⟩ := p.derivative_quartic_defect
  have hm := p.mass_pos
  refine ⟨K/(2*p.mass),by positivity,?_⟩
  intro z hz
  have hv : p.value z ≠ 0 := fun he => by have hi := p.value_im_pos hz; simp [he] at hi
  have hvc : conj (p.value z) ≠ 0 := by simpa using hv
  have h : dbar (logInput p.value) z-((‖p.value z‖^2/(2*p.mass):ℝ):ℂ) =
      (p.value z/conj (p.value z))*conj ((p.mass:ℂ)*deriv p.value z-(p.value z)^2)/(2*(p.mass:ℂ)) := by
    rw [dbar_logInput (p.hasDerivAt hz).differentiableAt.hasDerivAt hv]
    simp only [Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_mul,Complex.ofReal_ofNat,
      ←Complex.mul_conj',map_sub,map_mul,map_pow,Complex.conj_ofReal]
    field_simp [hvc,Complex.ofReal_ne_zero.mpr hm.ne'] <;> ring
  rw [h,norm_div,norm_mul,norm_div,Complex.norm_conj,Complex.norm_conj,div_self (norm_ne_zero_iff.mpr hv),
    one_mul,norm_mul,Complex.norm_two,Complex.norm_of_nonneg hm.le]
  calc
    _ ≤ (K/(1+‖z‖)^4)/(2*p.mass) := div_le_div_of_nonneg_right (hq z hz) (by positivity)
    _ = _ := by ring

theorem PickSum.logSource_conjugation_defect {n : ℕ} (p : PickSum n) :
    ∃ C > 0, ∀ z : ℂ, 0 ≤ z.im →
      ‖dbar (logInput p.value) z-conj (dbar (logInput p.value) z)‖ ≤ C/(1+‖z‖)^4 := by
  obtain ⟨K,hK,h⟩ := p.logSource_realModel_error
  refine ⟨2*K,by positivity,?_⟩
  intro z hz
  let r : ℝ := ‖p.value z‖^2/(2*p.mass)
  let d := dbar (logInput p.value) z
  have he : d-conj d = (d-(r:ℂ))-conj (d-(r:ℂ)) := by simp
  change ‖d-conj d‖ ≤ _
  rw [he]
  apply (norm_sub_le ..).trans
  rw [Complex.norm_conj]
  change ‖d-(r:ℂ)‖+‖d-(r:ℂ)‖ ≤ _
  have hh : ‖d-(r:ℂ)‖ ≤ K/(1+‖z‖)^4 := h z hz
  calc
    _ ≤ K/(1+‖z‖)^4 + K/(1+‖z‖)^4 := add_le_add hh hh
    _ = _ := by ring

end Liu
