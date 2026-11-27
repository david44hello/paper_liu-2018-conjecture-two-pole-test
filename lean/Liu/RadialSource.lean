module

public import Liu.FrozenSource
public import Liu.EnergyEstimate

@[expose] public section

noncomputable section
open Set Real
open scoped ComplexConjugate
namespace Liu

/-- Actual source in Lemma 2.3, including its complex phase and coefficient.
The error after subtracting the radial model is uniformly cubic at infinity. -/
theorem PickSum.source_far_model {n : ℕ} (p : PickSum n) :
    ∃ C ≥ 0, ∀ z : ℂ, 0≤z.im → 1<‖z‖ →
      ‖source p.value z-Complex.I*((p.mass/(2*‖z‖^2):ℝ):ℂ)‖ ≤ C/‖z‖^3 := by
  obtain ⟨K,hK,h₁⟩ := p.logSource_realModel_error
  obtain ⟨B,hB,h₂⟩ := p.power_tail_error
  have hm := p.mass_pos
  refine ⟨K+B/(2*p.mass),by positivity,?_⟩
  intro z hz hr
  have hv : p.value z≠0 := fun e => by have h := p.value_im_pos hz; simp [e] at h
  have hsrc : source p.value z=Complex.I*dbar (logInput p.value) z := by
    rw [dbar_logInput (p.hasDerivAt hz).differentiableAt.hasDerivAt hv]
    unfold source; ring
  rw [hsrc,←mul_sub,norm_mul,Complex.norm_I,one_mul]
  let r := ‖z‖
  have hp := zero_lt_one.trans hr
  have hmod := h₂ (2:ℝ) (by constructor <;> norm_num) z hz hr
  simp only [rpow_neg (norm_nonneg z),rpow_ofNat] at hmod
  let b := ‖p.value z‖^2/(2*p.mass)
  have hcomp : |b-p.mass/(2*r^2)| ≤ (B/(2*p.mass))/r^3 := by
    have eqn : b-p.mass/(2*r^2)=(‖p.value z‖^2-p.mass^2*(r^2)⁻¹)/(2*p.mass) := by
      dsimp [b]; field_simp [hm.ne',hp.ne'] <;> ring
    rw [eqn,abs_div,abs_of_pos (mul_pos (by norm_num) hm)]
    apply (div_le_div_of_nonneg_right hmod (by positivity : 0≤2*p.mass)).trans_eq
    dsimp only [r]; ring
  have hden : r^3 ≤ (1+‖z‖)^4 := by
    change r^3 ≤ (1+r)^4
    have h3 := pow_le_pow_left₀ hp.le (by linarith : r ≤ 1+r) 3
    have h4 := mul_le_mul_of_nonneg_left (by linarith : 1≤1+r) (by positivity : 0≤(1+r)^3)
    nlinarith only [h3,h4]
  have hnear := (h₁ z hz).trans (div_le_div_of_nonneg_left hK.le (pow_pos hp 3) hden)
  have hnorm := norm_sub_le_norm_sub_add_norm_sub (dbar (logInput p.value) z) (b:ℂ) (((p.mass/(2*r^2)):ℝ):ℂ)
  rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at hnorm
  apply hnorm.trans
  exact (add_le_add hnear hcomp).trans_eq (add_div ..).symm

end Liu
