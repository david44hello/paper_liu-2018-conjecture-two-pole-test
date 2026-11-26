import Liu.TraceBound

noncomputable section
open Set MeasureTheory Real
namespace Liu

theorem linePole_square_integral (a : ℝ) {b : ℝ} (hb : 0<b) :
    ∫ x, ‖linePole a b x‖^2 = π/b := by
  have he (x : ℝ) : ‖linePole a b x‖^2 = poissonLine a b x / b := by
    simp only [linePole_sq,poissonLine]
    field_simp [hb.ne']
  simp_rw [he,integral_div,poissonLine_integral a hb]

theorem pole_on_line (m a b x : ℝ) :
    pole m ((a:ℂ)-(b:ℂ)*Complex.I) (x:ℂ) = -(m:ℂ)*linePole a b x := by
  have h : (x:ℂ)-((a:ℂ)-(b:ℂ)*Complex.I) = ((x-a:ℝ):ℂ)+(b:ℂ)*Complex.I := by push_cast; ring
  simp only [pole,linePole,h,div_eq_mul_inv]

/-- The precise single-pole cancellation from Remark 5.2 for every mass, foot
and positive depth. The calculation uses the actual boundary field and dx/π. -/
theorem single_pole_flux_zero (a : ℝ) {m b : ℝ} (hm : 0 < m) (hb : 0 < b) :
    (∫ x : ℝ, ‖field (pole m ((a:ℂ)-(b:ℂ)*Complex.I)) x‖^2 -
      k₀*‖pole m ((a:ℂ)-(b:ℂ)*Complex.I) x‖^2)/π = 0 := by
  have hF (x : ℝ) : ‖field (pole m ((a:ℂ)-(b:ℂ)*Complex.I)) x‖^2 =
      m^2 * (isolatedTrace a b x)^2 := by
    rw [field_single_pole a x hm hb,norm_mul,norm_neg,Complex.norm_of_nonneg hm.le,
      Complex.norm_of_nonneg (isolatedTrace_nonneg a x hb),mul_pow]
  have hS (x : ℝ) : k₀ * ‖pole m ((a:ℂ)-(b:ℂ)*Complex.I) x‖^2 =
      (k₀*m^2)*‖linePole a b x‖^2 := by
    rw [pole_on_line,norm_mul,norm_neg,Complex.norm_of_nonneg hm.le,mul_pow]; ring
  have hfun := (div_eq_iff pi_ne_zero).mp (isolatedTrace_energy a hb)
  have hi : Integrable (fun x => (isolatedTrace a b x)^2) := Integrable.of_integral_ne_zero
    (hfun ▸ (by unfold k₀; positivity))
  simp_rw [hF,hS]
  rw [integral_sub (hi.const_mul _) ((linePole_sq_integrable a hb).const_mul _),
    integral_const_mul,integral_const_mul,hfun,linePole_square_integral a hb]
  ring

end Liu
