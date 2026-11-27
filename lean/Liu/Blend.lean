module

public import Liu.Witness

@[expose] public section

noncomputable section
open Real Complex
namespace Liu

/-- The argument on the unit disc centred at one. Jordan's inequality gives the
constant π/2 used in both the merged-pole and small-mass estimates. -/
theorem arg_one_add_bound {η : ℂ} (hη : ‖η‖ ≤ 1) : |arg (1+η)| ≤ π/2*‖η‖ := by
  let z := 1+η
  have hre : 0 ≤ z.re := by
    change 0 ≤ 1+η.re
    linarith [(abs_le.mp (abs_re_le_norm η)).1]
  have h := mul_abs_le_abs_sin (abs_arg_le_pi_div_two_iff.mpr hre)
  have hn : ‖z-1‖^2 = ‖z‖^2 + 1 - 2*z.re := by
    simp [Complex.sq_norm,Complex.normSq_apply]; ring
  have hsin : |Real.sin (arg z)| ≤ ‖z-1‖ := by
    have hl := Complex.norm_mul_cos_arg z
    have hs : |Real.sin (arg z)|^2 ≤ ‖z-1‖^2 := by
      rw [sq_abs,hn]
      nlinarith [Real.sin_sq_add_cos_sq (arg z),sq_nonneg (‖z‖-Real.cos (arg z))]
    exact le_of_sq_le_sq hs (norm_nonneg _)
  have hh := h.trans hsin
  have hπ := pi_pos
  dsimp [z] at hh
  rw [add_sub_cancel_left] at hh
  field_simp at hh
  nlinarith

def blendedError (A B : ℂ) : ℂ :=
  A*(arg (1+B/A):ℂ) + B*(arg (1+A/B):ℂ)

private theorem blendedError_small {A B : ℂ} (hA : A ≠ 0) (hB : ‖B‖ ≤ ‖A‖) :
    ‖blendedError A B‖ ≤ (3*π/2)*‖B‖ := by
  have ha := norm_pos_iff.mpr hA
  have hq : ‖B/A‖ ≤ 1 := by rw [norm_div]; exact (div_le_one ha).mpr hB
  have hl := arg_one_add_bound hq
  rw [norm_div] at hl
  have hu := Complex.abs_arg_le_pi (1+A/B)
  apply (norm_add_le _ _).trans
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ ‖A‖*(π/2*(‖B‖/‖A‖)) + ‖B‖*π :=
      add_le_add (mul_le_mul_of_nonneg_left hl (norm_nonneg _)) (mul_le_mul_of_nonneg_left hu (norm_nonneg _))
    _ = _ := by field_simp [ha.ne']; ring

theorem blendedError_bound {A B : ℂ} (hA : A ≠ 0) (hB : B ≠ 0) :
    ‖blendedError A B‖ ≤ (3*π/2)*min ‖B‖ ‖A‖ := by
  rcases le_total ‖B‖ ‖A‖ with hab | hba
  · rw [min_eq_left hab]; exact blendedError_small hA hab
  · rw [min_eq_right hba]
    simpa only [blendedError,add_comm] using blendedError_small hB hba

end Liu
