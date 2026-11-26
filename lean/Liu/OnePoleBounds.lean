import Liu.OnePoleIdentity

noncomputable section
open Set Real
namespace Liu

private theorem optimalWitness_scaled_at {S T : ℂ → ℂ} {z u : ℂ} {c : ℝ} (hc : 0<c)
    (hs : S z=(c:ℂ)*T u) (hv : field S z=(c:ℂ)*field T u) :
    optimalWitness S z=optimalWitness T u := by
  simp only [optimalWitness,hs,hv,Complex.arg_real_mul _ hc,mul_assoc,←mul_sub]
  exact mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr hc.ne')

/-- Appendix A.3(b), including the real boundary and arbitrary mass, depth and shift. -/
theorem singlePole_optimalWitness (x : ℝ) {a b : ℝ} (ha : 0<a) (hb : 0<b)
    {z : ℂ} (hz : 0≤z.im) :
    optimalWitness (pole a ((x:ℂ)-(b:ℂ)*Complex.I)) z=singleWitness ((z-(x:ℂ))/(b:ℂ)) := by
  let T := dilateFunction unitPolePick.value b⁻¹
  let Q := fun w : ℂ => T (w+((-x:ℝ):ℂ))
  let u := (z-(x:ℂ))/(b:ℂ)
  have hbC : (b:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have hT (w : ℂ) : T w = pole 1 (-((b:ℝ):ℂ)*Complex.I) w := by
    dsimp only [T,dilateFunction]
    rw [unitPolePick_value,Complex.real_smul,Complex.ofReal_inv]
    have hden : (b:ℂ)⁻¹*w- -Complex.I=(w-(-(b:ℂ)*Complex.I))/(b:ℂ) := by field_simp
    simp only [pole,hden,div_div_eq_mul_div,Complex.ofReal_one,div_eq_mul_inv]
    field_simp [hbC]
  have hs : pole a ((x:ℂ)-(b:ℂ)*Complex.I) = fun w => (a:ℂ)*Q w := by
    funext w
    dsimp only [Q]; rw [hT,Complex.ofReal_neg]
    simp only [pole,Complex.ofReal_one]
    rw [show w+- (x:ℂ)-(-(b:ℂ)*Complex.I)=w-((x:ℂ)-(b:ℂ)*Complex.I) by ring]; ring
  have hu : b⁻¹ • (z+((-x:ℝ):ℂ))=u := by simp [u,Complex.real_smul,div_eq_mul_inv,sub_eq_add_neg,mul_comm]; ring
  have hS : pole a ((x:ℂ)-(b:ℂ)*Complex.I) z=((a*b⁻¹:ℝ):ℂ)*unitPolePick.value u := by
    rw [hs]; dsimp only [Q,T,dilateFunction]; rw [hu,Complex.ofReal_mul,mul_assoc]
  have hF : field (pole a ((x:ℂ)-(b:ℂ)*Complex.I)) z=((a*b⁻¹:ℝ):ℂ)*field unitPolePick.value u := by
    rw [hs,field_mass_scale]
    dsimp only [Q,T]; rw [field_shift,field_dilate _ (inv_pos.mpr hb),hu,Complex.ofReal_mul,mul_assoc]
  rw [optimalWitness_scaled_at (mul_pos ha (inv_pos.mpr hb)) hS hF]
  apply unitPole_optimalWitness
  dsimp [u]; simp [div_eq_mul_inv,Complex.mul_im,Complex.mul_re]; positivity

/-- Appendix A.3(c,d), the two uniform numerical estimates for the actual optimal witness. -/
theorem singlePole_witness_bounds (x : ℝ) {a b : ℝ} (ha : 0<a) (hb : 0<b)
    {z : ℂ} (hz : 0≤z.im) :
    let S := pole a ((x:ℂ)-(b:ℂ)*Complex.I)
    let D := ((S z).arg:ℂ)-optimalWitness S z
    ‖D‖≤π/2+log 2 ∧ π/2+log 2<2.264 ∧ |D.re|<2.264 ∧ |k₀-‖D‖^2|<4.304 := by
  let S := pole a ((x:ℂ)-(b:ℂ)*Complex.I)
  let u := (z-(x:ℂ))/(b:ℂ)
  have hu : 0≤u.im := by dsimp [u]; simp [div_eq_mul_inv,Complex.mul_im,Complex.mul_re]; positivity
  have hSp : 0<(S z).im := by
    have h := (singlePick a x b ha hb).value_im_pos hz
    rwa [singlePick_value] at h
  obtain ⟨hα,hπ⟩ := upper_arg_range (show S z∈upper from hSp)
  let D := ((S z).arg:ℂ)-optimalWitness S z
  have hd : D=(((S z).arg-π/2:ℝ):ℂ)-omegaCorrection u := by
    dsimp only [D,S]; rw [singlePole_optimalWitness x ha hb hz,singleWitness]; push_cast; ring
  have hn : ‖D‖≤π/2+log 2 := by
    rw [hd]
    apply (norm_sub_le ..).trans
    rw [Complex.norm_real,Real.norm_eq_abs]
    exact add_le_add (abs_le.mpr ⟨by linarith,by linarith⟩) (omegaCorrection_bound hu)
  have hk : π/2+log 2<2.264 := by linarith [pi_lt_d6,log_two_lt_d9]
  have hu' := hn.trans_lt hk
  refine ⟨hn,hk,(Complex.abs_re_le_norm _).trans_lt hu',abs_lt.mpr ⟨?_,?_⟩⟩
  · change -4.304<π^2/12-‖D‖^2
    nlinarith only [sq_lt_sq' (by linarith [norm_nonneg D] : -(2.264:ℝ)<‖D‖) hu',
      mul_self_lt_mul_self (by norm_num : (0:ℝ)≤3.1415) pi_gt_d4]
  · change π^2/12-‖D‖^2<4.304
    nlinarith only [sq_nonneg ‖D‖,mul_self_lt_mul_self pi_pos.le pi_lt_d4]

end Liu
