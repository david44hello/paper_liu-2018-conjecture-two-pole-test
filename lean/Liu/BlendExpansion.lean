import Liu.Blend
import Liu.OnePoleBounds

noncomputable section
open Set Real
namespace Liu

def linearBlend (A B : ℂ) : ℂ := A*((B/A).im:ℂ)+B*((A.arg-B.arg:ℝ):ℂ)

theorem upper_arg_div {A B : ℂ} (hA : A∈upper) (hB : B∈upper) : (A/B).arg=A.arg-B.arg := by
  obtain ⟨ha,hπa⟩ := upper_arg_range hA
  obtain ⟨hb,hπb⟩ := upper_arg_range hB
  have hn {u : ℂ} (hu : u∈upper) : u≠0 := fun e => by simpa [e,upper] using hu
  have h := congrArg Real.Angle.toReal (Complex.arg_div_coe_angle (hn hA) (hn hB))
  simpa only [Complex.arg_coe_angle_toReal_eq_arg,←Real.Angle.coe_sub,
    Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr (show A.arg-B.arg∈Ioc (-π) π by constructor <;> linarith)] using h

theorem blendedError_identity {A B : ℂ} (hA : A∈upper) (hB : B∈upper) :
    blendedError A B=(A+B)*((A+B).arg:ℂ)-A*(A.arg:ℂ)-B*(B.arg:ℂ) := by
  have h : A+B∈upper := add_pos (show 0<A.im from hA) (show 0<B.im from hB)
  have hn {u : ℂ} (hu : u∈upper) : u≠0 := fun e => by simpa [e,upper] using hu
  rw [blendedError,show 1+B/A=(A+B)/A by field_simp [hn hA],
    show 1+A/B=(A+B)/B by field_simp [hn hB]; ring,upper_arg_div h hA,upper_arg_div h hB]
  push_cast; ring

theorem linearBlend_bound {A B : ℂ} (hA : A∈upper) (hB : B∈upper) :
    ‖linearBlend A B‖ ≤ 5*‖B‖ := by
  have hn : A≠0 := fun e => by simpa [e,upper] using hA
  have hθ := Complex.abs_arg_le_pi (B/A)
  rw [upper_arg_div hB hA,abs_sub_comm] at hθ
  change ‖A*_+B*_‖≤_
  apply (norm_add_le ..).trans
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  have h := Complex.abs_im_le_norm (B/A)
  rw [norm_div] at h
  have h' := (le_div_iff₀ (norm_pos_iff.mpr hn)).mp h
  nlinarith only [h',mul_le_mul_of_nonneg_left (hθ.trans (show π≤4 by linarith [pi_lt_d2])) (norm_nonneg B)]

/-- Subtract the exact linearization before estimating the logarithm. -/
theorem blendedError_sub_linear {A B : ℂ} (hA : A∈upper) (hB : B∈upper) {m : ℝ} (hm : 0 < m) :
    let ξ := (m:ℂ)*B/A
    let δ := (1+ξ).arg
    blendedError A ((m:ℂ)*B)-(m:ℂ)*linearBlend A B =
      A*((δ-ξ.im:ℝ):ℂ)+((m:ℂ)*B)*(δ:ℂ) := by
  have hmB : ((m:ℂ)*B)∈upper := by simpa [upper,Complex.mul_im] using mul_pos hm (show 0<B.im from hB)
  have hn : A≠0 := fun e => by simpa [e,upper] using hA
  have ha : (1+(m:ℂ)*B/A).arg=(A+(m:ℂ)*B).arg-A.arg := by
    rw [show 1+(m:ℂ)*B/A=(A+(m:ℂ)*B)/A by field_simp [hn]]
    exact upper_arg_div (show A+(m:ℂ)*B∈upper from add_pos (show 0<A.im from hA) (show 0<((m:ℂ)*B).im from hmB)) hA
  dsimp only
  rw [blendedError_identity hA hmB,Complex.arg_real_mul _ hm,ha,
    show (m:ℂ)*B/A=(m:ℂ)*(B/A) by ring,linearBlend]
  simp [Complex.mul_im]; push_cast; ring

theorem arg_log_quadratic {ξ : ℂ} (hξ : ‖ξ‖≤3/5) :
    |(1+ξ).arg-ξ.im| ≤ 2*‖ξ‖^2 := by
  have h := Complex.norm_log_one_add_sub_self_le (show ‖ξ‖<1 by linarith)
  have h' := (Complex.abs_im_le_norm (Complex.log (1+ξ)-ξ)).trans h
  rw [Complex.sub_im,Complex.log_im] at h'
  apply h'.trans
  have hd : (1-‖ξ‖)⁻¹≤4 := by
    rw [←one_div,div_le_iff₀ (show 0<1-‖ξ‖ by linarith)]
    linarith
  nlinarith only [mul_le_mul_of_nonneg_left hd (sq_nonneg ‖ξ‖)]

theorem onePole_field_bound {w z : ℂ} (hw : w.im<0) (hz : 0≤z.im) :
    ‖field (pole 1 w) z‖ ≤ (5/2)*‖pole 1 w z‖ := by
  let S := pole 1 w
  have he : (w.re:ℂ)-((-w.im:ℝ):ℂ)*Complex.I=w := by apply Complex.ext <;> simp
  have h := singlePole_witness_bounds w.re zero_lt_one (neg_pos.mpr hw) hz
  dsimp only at h; rw [he] at h
  have hn : S z≠0 := fun e => by have h := pole_im_pos zero_lt_one hw hz; change 0<(S z).im at h; simp [e] at h
  have hf : field S z=S z*(((S z).arg:ℂ)-optimalWitness S z) := by unfold optimalWitness; field_simp [hn]; ring
  change ‖field S z‖≤_
  rw [hf,norm_mul,mul_comm (5/2:ℝ)]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  linarith [h.1.trans_lt h.2.1]

end Liu
