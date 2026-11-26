import Liu.ChebyshevEllipse
import Liu.ChebyshevAlias
import Mathlib.Analysis.Fourier.AddCircle

noncomputable section
open Real Set MeasureTheory Metric Polynomial Polynomial.Chebyshev Complex
open scoped Topology ComplexConjugate
namespace Liu

local instance : Fact (0<(2*π:ℝ)) := ⟨two_pi_pos⟩

private theorem real_segment_in_ellipse {ρ x : ℝ} (hρ : 1<ρ) (hx : x∈Icc (-1:ℝ) 1) :
    (x:ℂ)∈bernsteinEllipse ρ := by
  have hr := zero_lt_one.trans hρ
  change ‖(x:ℂ)-1‖+‖(x:ℂ)+1‖≤ρ+ρ⁻¹
  rw [←Complex.ofReal_one,←Complex.ofReal_sub,←Complex.ofReal_add,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonpos (by linarith [hx.2]),abs_of_nonneg (by linarith [hx.1])]
  rw [←one_div]
  field_simp [hr.ne']
  nlinarith [sq_nonneg (ρ-1)]

private def circleLift {ρ : ℝ} (hρ : 1<ρ) {χ : ℂ → ℂ} (ha : AnalyticOnNhd ℂ χ (bernsteinEllipse ρ)) :
    C(AddCircle (2*π),ℂ) where
  toFun θ := χ (((fourier 1 θ).re:ℝ):ℂ)
  continuous_toFun := by
    apply ha.continuousOn.comp_continuous (by fun_prop)
    intro θ
    apply real_segment_in_ellipse hρ
    have h := Complex.abs_re_le_norm (fourier 1 θ)
    rw [show ‖fourier 1 θ‖=1 from Circle.norm_coe _] at h
    exact abs_le.mp h

private theorem fourier_angle (k : ℤ) (t : ℝ) :
    fourier k (t:AddCircle (2*π)) = Complex.exp ((k:ℂ)*t*I) := by
  rw [fourier_coe_apply]; congr 1; push_cast; field_simp [Complex.ofReal_ne_zero.mpr pi_ne_zero] <;> ring

private theorem circleLift_coe {ρ : ℝ} (hρ : 1<ρ) {χ : ℂ → ℂ} (ha : AnalyticOnNhd ℂ χ (bernsteinEllipse ρ)) (t : ℝ) :
    circleLift hρ ha (t:AddCircle (2*π))=χ (Real.cos t) := by
  change χ (((fourier 1 (t:AddCircle (2*π))).re:ℝ):ℂ)=_
  rw [fourier_angle]; simp [Complex.exp_re]

private theorem cheb_integral_fourier {χ : ℂ → ℂ} {ρ : ℝ} (hρ : 1<ρ)
    (ha : AnalyticOnNhd ℂ χ (bernsteinEllipse ρ)) (k : ℤ) (b : ℝ) :
    fourierCoeff (circleLift hρ ha) k=(1/(2*π):ℝ) •
      ∫ t in b..b+2*π, Complex.exp ((-k:ℂ)*t*I)*χ (Real.cos t) := by
  rw [fourierCoeff_eq_intervalIntegral _ _ b]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  simp only [smul_eq_mul,fourier_angle,circleLift_coe,Int.cast_neg]

private theorem coefficient_fourier_eq {χ : ℂ → ℂ} {ρ : ℝ} (hρ : 1<ρ)
    (ha : AnalyticOnNhd ℂ χ (bernsteinEllipse ρ)) (n : ℕ) :
    ellipseCoefficient χ n=fourierCoeff (circleLift hρ ha) (n:ℤ) := by
  rw [cheb_integral_fourier hρ ha _ 0,zero_add]
  let F := fun t : ℝ => Complex.exp (-(n:ℂ)*t*I)*χ (Real.cos t)
  have he (t : ℝ) : deriv (circleMap 0 1) t • (χ (joukowski (circleMap 0 1 t))/(circleMap 0 1 t)^(n+1))=I*F t := by
    let w := Complex.exp ((t:ℂ)*I)
    have hn : w≠0 := Complex.exp_ne_zero _
    have hj : joukowski w=((Real.cos t:ℝ):ℂ) := by
      simp [joukowski,w,Complex.ofReal_cos,Complex.cos,neg_mul,Complex.exp_neg]
    have hp : Complex.exp (-(n:ℂ)*t*I)=(w^n)⁻¹ := by
      rw [show -(n:ℂ)*t*I= -((n:ℂ)*((t:ℂ)*I)) by ring,Complex.exp_neg,Complex.exp_nat_mul]
    rw [deriv_circleMap]; simp only [circleMap,Complex.ofReal_one,zero_add,one_mul,smul_eq_mul]
    change (w*I)*(χ (joukowski w)/w^(n+1))=I*F t
    rw [hj]; dsimp only [F]; rw [hp]; field_simp [hn] <;> ring
  unfold ellipseCoefficient circleIntegral
  simp_rw [he,intervalIntegral.integral_const_mul]
  simp only [Int.cast_natCast,Complex.real_smul,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_mul,Complex.ofReal_ofNat,smul_eq_mul]
  dsimp [F]; field_simp [I_ne_zero,Complex.ofReal_ne_zero.mpr pi_ne_zero] <;> ring

private theorem coefficient_fourier_even {χ : ℂ → ℂ} {ρ : ℝ} (hρ : 1<ρ)
    (ha : AnalyticOnNhd ℂ χ (bernsteinEllipse ρ)) (k : ℤ) :
    fourierCoeff (circleLift hρ ha) (-k)=fourierCoeff (circleLift hρ ha) k := by
  rw [cheb_integral_fourier hρ ha _ (-π),cheb_integral_fourier hρ ha _ (-π),
    show -π+2*π=π by ring]
  congr 1
  let F := fun t : ℝ => Complex.exp (-(k:ℂ)*t*I)*χ (Real.cos t)
  have he (t : ℝ) : Complex.exp (-((-k:ℤ):ℂ)*t*I)*χ (Real.cos t)=F (-t) := by
    dsimp [F]; rw [Real.cos_neg,Complex.ofReal_neg,Int.cast_neg]; congr 2; ring
  simp_rw [he,intervalIntegral.integral_comp_neg,neg_neg]; rfl

/-- Fourier coefficients of the cosine lift decay geometrically in both
directions. This proves absolute convergence before evaluating the series. -/
theorem ellipse_cosine_series {χ : ℂ → ℂ} {ρ M : ℝ} (hρ : 1<ρ)
    (ha : AnalyticOnNhd ℂ χ (bernsteinEllipse ρ)) (hM : ∀ z∈bernsteinEllipse ρ, ‖χ z‖≤M) :
    ∃ b : ℤ → ℂ, (∀ k : ℤ, ‖b k‖≤M/ρ^k.natAbs) ∧
      ∀ x : ℝ, x∈Icc (-1:ℝ) 1 →
        HasSum (fun k : ℤ => b k*(T ℂ k).eval (x:ℂ)) (χ (x:ℂ)) := by
  let f := circleLift hρ ha
  let b := fourierCoeff f
  have hbd (k : ℤ) : ‖b k‖≤M/ρ^k.natAbs := by
    cases k with
    | ofNat n =>
      change ‖fourierCoeff (circleLift hρ ha) (n:ℤ)‖≤M/ρ^n
      rw [←coefficient_fourier_eq]; exact ellipse_coefficient_bound hρ ha hM n
    | negSucc n =>
      change ‖fourierCoeff (circleLift hρ ha) (-((n+1:ℕ):ℤ))‖≤M/ρ^(n+1)
      rw [coefficient_fourier_even,←coefficient_fourier_eq]; exact ellipse_coefficient_bound hρ ha hM _
  have hr : 0<ρ := zero_lt_one.trans hρ
  have hbnd : Summable (fun n : ℕ => M/ρ^n) := by
    simp only [div_eq_mul_inv,←inv_pow]
    exact (summable_geometric_of_lt_one (inv_pos.mpr hr).le (inv_lt_one_of_one_lt₀ hρ)).mul_left _
  have hnb : Summable b := .of_nat_of_neg_add_one (hbnd.of_norm_bounded (fun n => hbd n))
    (((summable_nat_add_iff 1).mpr hbnd).of_norm_bounded (fun n => hbd (-(n+1))))
  refine ⟨b,hbd,?_⟩
  intro x hx
  obtain ⟨t,_,rfl⟩ := surjOn_cos hx
  have hp := has_pointwise_sum_fourier_series_of_summable hnb (t:AddCircle (2*π))
  have hn := has_pointwise_sum_fourier_series_of_summable hnb ((-t:ℝ):AddCircle (2*π))
  have hpair := (hp.add hn).mul_right ((2:ℂ)⁻¹)
  simp only [f,circleLift_coe,Real.cos_neg] at hpair
  convert hpair using 1
  · funext k
    rw [Complex.ofReal_cos,T_complex_cos]
    simp only [smul_eq_mul,fourier_angle,b,f,Complex.cos,Complex.ofReal_neg]
    ring_nf
  · ring

end Liu
