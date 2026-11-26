import Liu.TrialExpansion

noncomputable section
open Set Real Complex
namespace Liu

private theorem log_near_one {t e : ℝ} (he : e≤1/2) (ht : |t-1|≤e) : |Real.log t|≤2*e := by
  have E := abs_le.mp ht
  have h₀ : 0<t := by linarith
  have hhalf : 1/2≤t := by linarith
  have he₀ := (abs_nonneg _).trans ht
  apply abs_le.mpr
  constructor
  · have h := Real.log_le_sub_one_of_pos (inv_pos.mpr h₀)
    rw [Real.log_inv] at h
    have hh : t⁻¹-1 ≤ 2*e := by
      rw [sub_le_iff_le_add,inv_le_comm₀ h₀ (by positivity),inv_le_comm₀ (by positivity) h₀]
      rw [inv_eq_one_div,div_le_iff₀ h₀]
      nlinarith [mul_le_mul_of_nonneg_left hhalf he₀]
    linarith
  · linarith [Real.log_le_sub_one_of_pos h₀]

/-- A global majorant for the compensated trial factor. At large relative
perturbations it uses cubic growth; near one the logarithm is Lipschitz. -/
theorem trialFactor_bound (w : ℂ) {d : ℝ} (hd : |d|≤1) :
    |trialFactor w d| ≤ 100*(1+‖w‖)^3 := by
  let N := ‖1-(d:ℂ)*w‖
  let e := |d| * ‖w‖
  have e₀ : 0≤e := mul_nonneg (abs_nonneg _) (norm_nonneg _)
  have hN : |N-1| ≤ e := by
    simpa [N,e,Complex.norm_real,Real.norm_eq_abs] using abs_norm_sub_norm_le (1-(d:ℂ)*w) (1:ℂ)
  have hN₀ : 0≤N := norm_nonneg _
  have re := Complex.abs_re_le_norm w
  have hd₂ : d^2=|d|^2 := (sq_abs d).symm
  by_cases hn : d=0
  · simp [trialFactor,hn]; positivity
  have hdpos := sq_pos_of_ne_zero hn
  rw [trialFactor,abs_div,abs_of_pos hdpos,div_le_iff₀ hdpos]
  change |N^(2+d)-1+2*d*w.re|≤_
  by_cases small : e≤1/2
  · have hn₀ : 0<N := by linarith [(abs_le.mp hN).1]
    have hN₁ : N≤3/2 := by linarith [(abs_le.mp hN).2]
    have hlog := log_near_one small hN
    have he : |Real.log N*d|≤1 := by rw [abs_mul]; nlinarith [mul_le_mul hlog hd (abs_nonneg _) (by positivity)]
    have hex := Real.abs_exp_sub_one_le he
    have H : |Real.exp (Real.log N*d)-1|≤4*d^2*‖w‖ := by
      rw [abs_mul] at hex
      calc
        _ ≤ 2*(2*e*|d|) := hex.trans (by gcongr)
        _ = _ := by rw [hd₂]; dsimp [e]; ring
    have sq := trial_sq w d
    change N^2=_ at sq
    have heq : N^(2+d)-1+2*d*w.re = N^2*(Real.exp (Real.log N*d)-1)+d^2*‖w‖^2 := by
      rw [Real.rpow_add hn₀,Real.rpow_two,Real.rpow_def_of_pos hn₀]
      linear_combination sq
    rw [heq]
    apply (abs_add_le ..).trans
    simp only [abs_mul,abs_of_nonneg (sq_nonneg N),abs_of_nonneg (sq_nonneg d),abs_of_nonneg (sq_nonneg ‖w‖)]
    apply (add_le_add (mul_le_mul (pow_le_pow_left₀ hN₀ hN₁ 2) H (abs_nonneg _) (by norm_num)) le_rfl).trans
    have hpoly : (3/2:ℝ)^2*(4*‖w‖)+‖w‖^2≤100*(1+‖w‖)^3 := by
      nlinarith [norm_nonneg w,sq_nonneg ‖w‖,pow_nonneg (norm_nonneg w) 3]
    nlinarith only [mul_le_mul_of_nonneg_right hpoly hdpos.le]
  · have he : 1/2<e := lt_of_not_ge small
    have hp : 0≤2+d := by linarith [(abs_le.mp hd).1]
    have hP : N^(2+d)≤(1+e)^3 := by
      apply (Real.rpow_le_rpow hN₀ (show N≤1+e by linarith [(abs_le.mp hN).2]) hp).trans
      rw [←Real.rpow_natCast (1+e) 3]
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      norm_num; linarith [(abs_le.mp hd).2]
    have hlinear : |2*d*w.re|≤2*e := by
      simp only [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]; dsimp [e]; linarith [mul_le_mul_of_nonneg_left re (abs_nonneg d)]
    have hfirst : |N^(2+d)-1+2*d*w.re| ≤ (1+e)^3+1+2*e := by
      exact (abs_add_le ..).trans (add_le_add ((abs_sub ..).trans (by simpa [abs_of_nonneg (Real.rpow_nonneg hN₀ _)] using add_le_add_left hP 1)) hlinear)
    have H : (1+e)^3+1+2*e ≤ 30*e^2+e^3 := by
      nlinarith [mul_le_mul_of_nonneg_right he.le e₀,sq_nonneg (e-1/2)]
    have hb : e^3≤d^2*‖w‖^3 := by
      dsimp [e]; rw [mul_pow,hd₂,pow_succ |d| 2]
      nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (sq_nonneg |d|)) (pow_nonneg (norm_nonneg w) 3)]
    have hg : 30*‖w‖^2+‖w‖^3≤100*(1+‖w‖)^3 := by nlinarith [norm_nonneg w,sq_nonneg ‖w‖,pow_nonneg (norm_nonneg w) 3]
    apply hfirst.trans (H.trans _)
    have e₂ : e^2=d^2*‖w‖^2 := by dsimp [e]; rw [mul_pow,sq_abs]
    rw [e₂]
    nlinarith only [hb,mul_le_mul_of_nonneg_right hg hdpos.le]

end Liu
