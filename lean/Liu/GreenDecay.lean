import Liu.KernelWeight
import Liu.GreenBoundary

noncomputable section
open Set MeasureTheory Real
namespace Liu

/-- The Dirichlet Green operator for minus the Laplacian, with area dx dy / π. -/
def greenOperator (ρ : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1/2:ℝ) • ∫ w, (greenLog z w:ℂ)*ρ w ∂upperArea

theorem scaled_inverse_near {z w : ℂ} {R : ℝ} (hR : 0<R) (hd : ‖z-w‖ < R/2) :
    localInverse (R⁻¹ • z) (R⁻¹ • w) = R*‖z-w‖⁻¹ := by
  have hs : ‖R⁻¹ • z-R⁻¹ • w‖ = R⁻¹*‖z-w‖ := by
    rw [←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)]
  have hm : R⁻¹ • w ∈ Metric.ball (R⁻¹ • z) 1 := by
    rw [Metric.mem_ball,dist_eq_norm,norm_sub_rev,hs,inv_mul_eq_div]
    exact (div_lt_one hR).mpr (by linarith)
  rw [localInverse,indicator_of_mem hm,hs,mul_inv_rev,inv_inv,mul_comm]

/-- A common cubic bound and a common integrable majorant for the vertical moment
give one Green bound for all sources satisfying those estimates. -/
theorem green_moment_estimate {K : ℝ} (hK : 0≤K) {H : ℂ → ℝ}
    (hint : Integrable H volume) (hpos : ∀ w, 0 ≤ H w) :
    ∃ C ≥ 0, ∀ ρ : ℂ → ℂ, Measurable ρ →
      (∀ w ∈ upper, ‖ρ w‖ ≤ K/(1+‖w‖)^3) → (∀ w ∈ upper, w.im*‖ρ w‖ ≤ H w) →
      ∀ z : ℂ, 0 ≤ z.im →
        Integrable (fun w => (greenLog z w:ℂ)*ρ w) upperArea ∧
        ‖greenOperator ρ z‖ ≤ C*z.im/(1+‖z‖)^2 := by
  classical
  let A := ∫ w, localInverse 0 w
  have hA : 0≤A := integral_nonneg fun w => indicator_nonneg (fun v _ => inv_nonneg.mpr (norm_nonneg _)) _
  have hB : 0 ≤ ∫ w, H w := integral_nonneg (fun w => hpos w)
  refine ⟨(1/2)*(1/π)*(16*K*A+8*∫ w, H w),by positivity,?_⟩
  intro ρ hm hsrc hmom z hz
  let R := 1+‖z‖
  have hR : 0<R := by dsimp [R]; positivity
  let L := fun w : ℂ => localInverse (R⁻¹ • z) (R⁻¹ • w)
  have hi : Integrable L volume := (localInverse_integrable _).comp_smul (inv_ne_zero hR.ne')
  have hi0 (w : ℂ) : 0 ≤ L w := indicator_nonneg (fun v _ => inv_nonneg.mpr (norm_nonneg _)) _
  have hiA : ∫ w, L w = R^2*A := by
    simpa [L,A] using scaled_localInverse_integral (R⁻¹ • z) R⁻¹ (inv_pos.mpr hR)
  let g := fun w => (16*K*z.im/R^4)*L w + (8*z.im/R^2)*H w
  have hg : Integrable g volume := (hi.const_mul _).add (hint.const_mul _)
  let f := fun w : ℂ => (greenLog z w:ℂ)*ρ w
  have hf : Measurable f := by dsimp [f,greenLog]; fun_prop
  have hb (w : ℂ) : ‖upper.indicator f w‖ ≤ g w := by
    have hleft : 0≤(16*K*z.im/R^4)*L w := by have := hi0 w; positivity
    have hright : 0≤(8*z.im/R^2)*H w := by have := hpos w; positivity
    by_cases hw : w ∈ upper
    · rw [indicator_of_mem hw]
      change ‖(greenLog z w:ℂ)*ρ w‖ ≤ _
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      by_cases near : ‖z-w‖ < R/2
      · apply le_trans _ (le_add_of_nonneg_right hright)
        have hW : 0 < 1+‖w‖ := by positivity
        have hgeom : R ≤ 2*(1+‖w‖) := by
          have ht := norm_add_le (z-w) w
          rw [sub_add_cancel] at ht
          dsimp [R] at near ⊢
          linarith
        have hc := pow_le_pow_left₀ hR.le hgeom 3
        have hsmall : ‖ρ w‖ ≤ 8*K/R^3 := (hsrc w hw).trans (by
          apply (div_le_div_iff₀ (pow_pos hW 3) (pow_pos hR 3)).mpr
          nlinarith only [mul_le_mul_of_nonneg_left hc hK])
        have hk := greenLog_height_bound hz hw
        calc
          _ ≤ (2*z.im*‖z-w‖⁻¹)*(8*K/R^3) := mul_le_mul hk hsmall (norm_nonneg _) (by positivity)
          _ = (16*K*z.im/R^4)*L w := by
            rw [show L w=R*‖z-w‖⁻¹ from scaled_inverse_near hR near]
            field_simp [hR.ne'] <;> ring
      · apply le_trans _ (le_add_of_nonneg_left hleft)
        have hd : 0 < ‖z-w‖ := lt_of_lt_of_le (half_pos hR) (le_of_not_gt near)
        have hne : z≠w := sub_ne_zero.mp (norm_pos_iff.mp hd)
        obtain ⟨hn,hk⟩ := greenLog_nonneg_le z w hz hw hne
        rw [abs_of_nonneg hn]
        have hden := pow_le_pow_left₀ (half_pos hR).le (le_of_not_gt near) 2
        have hk' : greenLog z w ≤ (8*z.im/R^2)*w.im := hk.trans (by
          rw [div_mul_eq_mul_div]
          apply (div_le_div_iff₀ (sq_pos_of_pos hd) (sq_pos_of_pos hR)).mpr
          nlinarith only [mul_le_mul_of_nonneg_left hden (show 0≤8*z.im*w.im by exact mul_nonneg (by positivity) (le_of_lt hw))])
        calc
          _ ≤ ((8*z.im/R^2)*w.im)*‖ρ w‖ := mul_le_mul_of_nonneg_right hk' (norm_nonneg _)
          _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hmom w hw) (by positivity)
    · simpa [hw,g] using add_nonneg hleft hright
  have hiF : IntegrableOn f upper volume := (integrable_indicator_iff upper_open.measurableSet).mp
    (hg.mono' (hf.indicator upper_open.measurableSet).aestronglyMeasurable (ae_of_all _ hb))
  constructor
  · unfold upperArea area
    rw [Measure.restrict_smul]
    exact hiF.smul_measure ENNReal.ofReal_ne_top
  · have hh := norm_integral_le_of_norm_le hg (ae_of_all _ hb)
    rw [integral_indicator upper_open.measurableSet] at hh
    simp only [g,integral_add (hi.const_mul _) (hint.const_mul _),integral_const_mul,hiA] at hh
    unfold greenOperator upperArea area
    rw [Measure.restrict_smul,integral_smul_measure,ENNReal.toReal_ofReal (by positivity),
      norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤1/π),
      abs_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
    apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh (by positivity : 0≤1/π))
      (by norm_num : (0:ℝ)≤1/2)).trans
    change _ ≤ (1/2)*(1/π)*(16*K*A+8*∫ w, H w)*z.im/R^2
    apply le_of_eq
    field_simp [hR.ne'] <;> ring

/-- The precise log-weighted fourth-order decay class used in Appendix B, Step 2. -/
theorem green_log_quartic_estimate {K : ℝ} (hK : 0≤K) :
    ∃ C ≥ 0, ∀ ρ : ℂ → ℂ, Measurable ρ →
      (∀ w ∈ upper, ‖ρ w‖ ≤ K*(1+log (2+‖w‖))/(1+‖w‖)^4) →
      ∀ z : ℂ, 0≤z.im →
        Integrable (fun w => (greenLog z w:ℂ)*ρ w) upperArea ∧
        ‖greenOperator ρ z‖ ≤ C*z.im/(1+‖z‖)^2 := by
  let L := K*(3+log 2)
  have hl2 : 0 ≤ log 2 := log_nonneg (by norm_num)
  have hL : 0≤L := by dsimp [L]; positivity
  let H := fun w : ℂ => L*(1+‖w‖)^(-(5/2:ℝ))
  have hint : Integrable H volume :=
    (integrable_one_add_norm (μ:=(volume:Measure ℂ)) (r:=5/2) (by norm_num)).const_mul L
  obtain ⟨C,hC,hbound⟩ := green_moment_estimate hL hint (fun w => by dsimp [H]; positivity)
  refine ⟨C,hC,?_⟩
  intro ρ hm hρ
  have hdec (w : ℂ) (hw : w ∈ upper) : ‖ρ w‖ ≤ L*(1+‖w‖)^(-(7/2:ℝ)) := by
    let R := 1+‖w‖
    have hr : 1≤R := by dsimp [R]; linarith [norm_nonneg w]
    have hR := zero_lt_one.trans_le hr
    have hu : 1≤R^(1/2:ℝ) := one_le_rpow hr (by norm_num)
    have hs := log_le_rpow_div hR.le (by norm_num : (0:ℝ)<1/2)
    have hl := log_le_log (by positivity : 0 < 2+‖w‖) (show 2+‖w‖ ≤ 2*R by dsimp [R]; linarith [norm_nonneg w])
    rw [log_mul (by norm_num) hR.ne'] at hl
    have hlog : 1+log (2+‖w‖) ≤ (3+log 2)*R^(1/2:ℝ) := by
      nlinarith [mul_nonneg hl2 (sub_nonneg.mpr hu)]
    apply (hρ w hw).trans
    calc
      _ ≤ K*((3+log 2)*R^(1/2:ℝ))/R^4 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlog hK) (by positivity)
      _ = L*R^(-(7/2:ℝ)) := by
        rw [show R^(4:ℕ)=R^(4:ℝ) by norm_num,div_eq_mul_inv,←rpow_neg hR.le]
        dsimp only [L]
        rw [mul_assoc K, mul_assoc,←rpow_add hR]
        norm_num <;> ring
  apply hbound ρ hm
  · intro w hw
    have hr : 1≤1+‖w‖ := by linarith [norm_nonneg w]
    have hp := rpow_le_rpow_of_exponent_le hr (by norm_num : -(7/2:ℝ) ≤ -(3:ℝ))
    simpa [rpow_neg (by positivity : 0≤1+‖w‖),div_eq_mul_inv] using
      (hdec w hw).trans (mul_le_mul_of_nonneg_left hp hL)
  · intro w hw
    have h := mul_le_mul ((Complex.im_le_norm w).trans (by linarith : ‖w‖≤1+‖w‖)) (hdec w hw)
      (norm_nonneg _) (by positivity : 0≤1+‖w‖)
    apply h.trans
    dsimp only [H]
    rw [mul_left_comm,show -(5/2:ℝ) = 1+ -(7/2:ℝ) by norm_num,rpow_add (by positivity : 0<1+‖w‖),rpow_one]

end Liu
