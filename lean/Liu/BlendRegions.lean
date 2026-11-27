module

public import Liu.BlendExpansion

@[expose] public section

noncomputable section
open Set Real
namespace Liu

private theorem arg_linear_bound {v : ℂ} (hv : ‖v‖≤1) : |(1+v).arg|≤2*‖v‖ :=
  (arg_one_add_bound hv).trans (mul_le_mul_of_nonneg_right (by linarith [pi_lt_d2]) (norm_nonneg _))

theorem blend_remainder_near {A B : ℂ} {m : ℝ} (hA : A∈upper) (hB : B∈upper) (hm : 0 < m)
    (hξ : ‖(m:ℂ)*B/A‖≤3/5) :
    ‖A‖*‖blendedError A ((m:ℂ)*B)-(m:ℂ)*linearBlend A B‖ ≤ 4*m^2*‖B‖^2 := by
  let ξ := (m:ℂ)*B/A
  have hA' : A≠0 := fun e => by simpa [e,upper] using hA
  have hr : ‖A‖*‖ξ‖=m*‖B‖ := by
    dsimp [ξ]; rw [norm_div,norm_mul,Complex.norm_of_nonneg hm.le]; field_simp [norm_ne_zero_iff.mpr hA']
  have hδ := arg_linear_bound (v:=ξ) (by linarith [show ‖ξ‖≤3/5 from hξ])
  have h := blendedError_sub_linear hA hB hm
  dsimp only at h
  rw [h]
  apply (mul_le_mul_of_nonneg_left (norm_add_le ..) (norm_nonneg A)).trans
  simp only [norm_mul,Complex.norm_of_nonneg hm.le,Complex.norm_real,Real.norm_eq_abs]
  change ‖A‖*(‖A‖*|(1+ξ).arg-ξ.im|+m*‖B‖*|(1+ξ).arg|)≤_
  apply (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left (arg_log_quadratic hξ) (norm_nonneg A))
    (mul_le_mul_of_nonneg_left hδ (by positivity : 0≤ m*‖B‖))) (norm_nonneg A)).trans_eq
  calc
    _ = 2*(‖A‖*‖ξ‖)^2+2*(m*‖B‖)*(‖A‖*‖ξ‖) := by ring
    _ = _ := by rw [hr] <;> ring

theorem blend_far_bounds {A B e : ℂ} {m : ℝ} (hA : A∈upper) (hB : B∈upper)
    (hm : 0 < m) (hm' : m≤1/10) (he : B/A=1+e) (he' : ‖e‖≤1/2) (hAB : ‖A‖≤2*‖B‖) :
    ‖blendedError A ((m:ℂ)*B)‖ ≤ 7*m*‖B‖*‖e‖ ∧
    ‖blendedError A ((m:ℂ)*B)-(m:ℂ)*linearBlend A B‖ ≤ 6*m^2*‖B‖*‖e‖ := by
  let ξ := (m:ℂ)*B/A
  let η := ((m/(1+m):ℝ):ℂ)*e
  have hmp : 0<1+m := by linarith
  have hn : (1+(m:ℂ))≠0 := by exact_mod_cast hmp.ne'
  have heq : ξ=(m:ℂ)+((1+m:ℝ):ℂ)*η := by
    dsimp [ξ,η]; push_cast; rw [mul_div_assoc,he]; field_simp [hn] <;> ring
  have hid : 1+ξ=((1+m:ℝ):ℂ)*(1+η) := by rw [heq]; push_cast; ring
  have hη : ‖η‖≤ m*‖e‖ := by
    dsimp [η]; rw [norm_mul,Complex.norm_of_nonneg (div_nonneg hm.le hmp.le)]
    exact mul_le_mul_of_nonneg_right (div_le_self hm.le (by linarith)) (norm_nonneg _)
  have he0 := norm_nonneg e
  have hmη : m*‖e‖≤1/20 := (mul_le_mul hm' he' he0 (by norm_num)).trans_eq (by norm_num)
  have hδ : (1+ξ).arg=(1+η).arg := by rw [hid,Complex.arg_real_mul _ hmp]
  have h₁ : |(1+ξ).arg|≤2*(m*‖e‖) := by
    rw [hδ]; exact (arg_linear_bound (by linarith : ‖η‖≤1)).trans (by linarith)
  have hθ : |B.arg-A.arg|≤2*‖e‖ := by rw [←upper_arg_div hB hA,he]; exact arg_linear_bound (by linarith)
  have h₂ : |(1+ξ).arg-ξ.im|≤2*m^2*‖e‖ := by
    have H : (1+ξ).arg-ξ.im=((1+η).arg-η.im)-m*η.im := by rw [hδ,heq]; simp [Complex.mul_im]; ring
    rw [H]
    apply (abs_sub ..).trans
    rw [abs_mul,abs_of_pos hm]
    have hb := arg_log_quadratic (by linarith : ‖η‖≤3/5)
    have hi := (Complex.abs_im_le_norm η).trans hη
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ he0 he' 1) (by positivity : 0≤ m^2*‖e‖)
    simp only [pow_one] at hh
    nlinarith only [hb,pow_le_pow_left₀ (norm_nonneg η) hη 2,mul_le_mul_of_nonneg_left hi hm.le,hh]
  have h₃ : ‖A‖*|(1+ξ).arg|≤(2*‖B‖)*(2*(m*‖e‖)) := mul_le_mul hAB h₁ (abs_nonneg _) (by positivity)
  have h₄ : ‖A‖*|(1+ξ).arg-ξ.im|≤(2*‖B‖)*(2*m^2*‖e‖) := mul_le_mul hAB h₂ (abs_nonneg _) (by positivity)
  constructor
  · have hmB : ((m:ℂ)*B)∈upper := by simpa [upper,Complex.mul_im] using mul_pos hm (show 0<B.im from hB)
    have hsum : A+(m:ℂ)*B∈upper := add_pos (show 0<A.im from hA) (show 0<((m:ℂ)*B).im from hmB)
    have hnA : A≠0 := fun e => by simpa [e,upper] using hA
    have hδ' : (1+ξ).arg=(A+(m:ℂ)*B).arg-A.arg := by
      rw [show 1+ξ=(A+(m:ℂ)*B)/A by dsimp [ξ]; field_simp [hnA]]
      exact upper_arg_div hsum hA
    have hg : blendedError A ((m:ℂ)*B)=A*((1+ξ).arg:ℂ)+((m:ℂ)*B)*(((1+ξ).arg-(B.arg-A.arg):ℝ):ℂ) := by
      rw [blendedError_identity hA hmB,Complex.arg_real_mul _ hm,hδ']; push_cast; ring
    rw [hg]
    apply (norm_add_le ..).trans
    simp only [norm_mul,Complex.norm_of_nonneg hm.le,Complex.norm_real,Real.norm_eq_abs]
    have hrest := (abs_sub ..).trans (add_le_add h₁ hθ)
    have hm2 := mul_le_mul_of_nonneg_right (show 2*m≤1 by linarith) (by positivity : 0≤ m*‖B‖*‖e‖)
    nlinarith only [h₃,mul_le_mul_of_nonneg_left hrest (by positivity : 0≤ m*‖B‖),hm2]
  · rw [blendedError_sub_linear hA hB hm]
    apply (norm_add_le ..).trans
    simp only [norm_mul,Complex.norm_of_nonneg hm.le,Complex.norm_real,Real.norm_eq_abs]
    change ‖A‖*|(1+ξ).arg-ξ.im|+m*‖B‖*|(1+ξ).arg|≤_
    nlinarith only [h₄,mul_le_mul_of_nonneg_left h₁ (by positivity : 0≤ m*‖B‖)]

end Liu
