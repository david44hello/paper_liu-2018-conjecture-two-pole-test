module

public import Liu.Mass

@[expose] public section

noncomputable section
open MeasureTheory Set Real
namespace Liu

/-- The dimensionless double integral for the squared boundary trace of a single pole. -/
theorem unit_square_basel :
    (∫ u in Ioo (0:ℝ) 1, ∫ v in Ioo (0:ℝ) 1, (1-u*v)⁻¹) = π^2/6 := by
  let I := Ioo (0:ℝ) 1
  let μ := (volume:Measure ℝ).restrict I
  let G := fun (n : ℕ) (z : ℝ × ℝ) => z.1^n*z.2^n
  have hI (n : ℕ) : Integrable (fun x : ℝ => x^n) μ := by
    exact ((continuous_id.pow n).continuousOn.integrableOn_compact (μ:=volume) (isCompact_Icc (a:=(0:ℝ)) (b:=1))).mono_set Ioo_subset_Icc_self
  have hm (n : ℕ) : Integrable (G n) (μ.prod μ) := (hI n).mul_prod (hI n)
  have hi (n : ℕ) : (∫ x, x^n ∂μ) = 1/((n:ℝ)+1) := by
    change (∫ x in Ioo (0:ℝ) 1, x^n) = _
    rw [←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le zero_le_one,integral_pow]
    simp
  have hcoeff (n : ℕ) : ∫ z, G n z ∂μ.prod μ = 1/((n:ℝ)+1)^2 := by
    rw [show (∫ z, G n z ∂μ.prod μ) = (∫ x, x^n ∂μ)*(∫ x, x^n ∂μ) from integral_prod_mul ..,hi]
    field_simp <;> ring
  have hs : HasSum (fun n : ℕ => 1/((n:ℝ)+1)^2) (π^2/6) := by
    have base := hasSum_zeta_two
    rw [←hasSum_nat_add_iff' 1] at base
    simpa using base
  have good : ∀ᵐ z ∂μ.prod μ, z.1 ∈ I ∧ z.2 ∈ I := by
    dsimp only [μ]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)
  have hnorm (n : ℕ) : ∫ z, ‖G n z‖ ∂μ.prod μ = ∫ z, G n z ∂μ.prod μ := by
    apply integral_congr_ae
    filter_upwards [good] with z hz
    exact Real.norm_of_nonneg (mul_nonneg (pow_nonneg hz.1.1.le _) (pow_nonneg hz.2.1.le _))
  let F := fun z : ℝ × ℝ => (1-z.1*z.2)⁻¹
  have eqn : (fun z => ∑' n, G n z) =ᵐ[μ.prod μ] F := by
    filter_upwards [good] with z hz
    have hmul := mul_lt_one_of_nonneg_of_lt_one_left hz.1.1.le hz.1.2 hz.2.2.le
    simpa [G,F,mul_pow] using (hasSum_geometric_of_lt_one (mul_nonneg hz.1.1.le hz.2.1.le) hmul).tsum_eq
  have hsum := integral_tsum_of_summable_integral_norm hm (by simp_rw [hnorm,hcoeff]; exact hs.summable)
  have hval : ∫ z, F z ∂μ.prod μ = π^2/6 := by
    rw [←integral_congr_ae eqn,←hsum]
    simpa only [hcoeff] using hs.tsum_eq
  have hF : Integrable F (μ.prod μ) := Integrable.of_integral_ne_zero (hval ▸ (by positivity))
  rw [integral_prod F hF] at hval
  exact hval

/-- Change variables t=y(1+u)/(1-u) from (0,1) to the tail (y,∞). -/
theorem depthTail_substitution {y : ℝ} (hy : 0<y) (f : ℝ → ℝ) :
    ∫ t in Ioi y, f t = ∫ u in Ioo (0:ℝ) 1, 2*y/(1-u)^2*f (y*(1+u)/(1-u)) := by
  let φ := fun u : ℝ => y*(1+u)/(1-u)
  have map_eq : φ '' Ioo 0 1 = Ioi y := by
    ext t
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact (lt_div_iff₀ (sub_pos.mpr hu.2)).mpr (by nlinarith [mul_pos hy hu.1])
    · intro ht
      have ht' : y<t := ht
      have hden : 0<t+y := by linarith
      let u := (t-y)/(t+y)
      have hu0 : 0<u := div_pos (sub_pos.mpr ht') hden
      have hu1 : u<1 := (div_lt_one hden).mpr (by linarith)
      refine ⟨u,⟨hu0,hu1⟩,?_⟩
      dsimp [φ,u]; field_simp [hden.ne',hy.ne']; ring
  have deriv (u : ℝ) (hu : u ∈ Ioo (0:ℝ) 1) : HasDerivAt φ (2*y/(1-u)^2) u := by
    have idu := hasDerivAt_id u
    have hd := ((idu.const_add 1).const_mul y).div (idu.const_sub 1) (by simpa using (sub_pos.mpr hu.2).ne')
    convert hd using 1
    · rfl
    change 2*y/(1-u)^2 = _
    simp [id]
    ring
  have hinj : InjOn φ (Ioo 0 1) := by
    intro a ha b hb e
    have h := (div_eq_div_iff (sub_pos.mpr ha.2).ne' (sub_pos.mpr hb.2).ne').mp e
    nlinarith [mul_eq_zero.mp (show y*(a-b)=0 by nlinarith)]
  rw [←map_eq,integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun u hu => (deriv u hu).hasDerivWithinAt) hinj]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u _
  dsimp only
  rw [smul_eq_mul,abs_of_nonneg (by positivity)]

theorem single_trace_double_integral {y : ℝ} (hy : 0 < y) :
    (∫ t in Ioi y, ∫ s in Ioi y, ((t+y)*(s+y)*(t+s))⁻¹) = k₀/y := by
  let φ := fun u : ℝ => y*(1+u)/(1-u)
  let J := fun u : ℝ => 2*y/(1-u)^2
  rw [depthTail_substitution hy]
  calc
    _ = ∫ u in Ioo (0:ℝ) 1, (1/(2*y))*(∫ v in Ioo (0:ℝ) 1, (1-u*v)⁻¹) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      dsimp only
      rw [depthTail_substitution hy,←integral_const_mul,←integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro v hv
      have hp := mul_lt_one_of_nonneg_of_lt_one_left hu.1.le hu.2 hv.2.le
      have hu' := (sub_pos.mpr hu.2).ne'
      have hv' := (sub_pos.mpr hv.2).ne'
      have huv := (sub_pos.mpr hp).ne'
      have de (a : ℝ) (ha : a ∈ Ioo (0:ℝ) 1) : 0<φ a := div_pos (mul_pos hy (by linarith [ha.1])) (sub_pos.mpr ha.2)
      change J u*(J v*((φ u+y)*(φ v+y)*(φ u+φ v))⁻¹) = _
      have hU := de u hu
      have hV := de v hv
      have d1 : φ u+y≠0 := by positivity
      have d2 : φ v+y≠0 := by positivity
      have d3 : φ u+φ v≠0 := by positivity
      dsimp only [J]
      field_simp [hy.ne',hu',hv',huv,d1,d2,d3]
      dsimp [φ] at *
      field_simp [hu',hv',hy.ne'] <;> ring
    _ = _ := by rw [integral_const_mul,unit_square_basel,k₀]; ring

end Liu
