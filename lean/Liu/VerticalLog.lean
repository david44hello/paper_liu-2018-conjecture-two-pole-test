module

public import Liu.PickRationalLog

@[expose] public section

noncomputable section
open Complex Real Set
open scoped ComplexConjugate
namespace Liu

/-- Vertical-cut logarithms for lower nodes and upper partners. -/
def lowerNodeLog (z : ℂ) := Complex.log (-I*z) + (π/2:ℝ)*I
def upperNodeLog (z : ℂ) := Complex.log (I*z) - (π/2:ℝ)*I

theorem lowerNodeLog_principal {z : ℂ} (hz : 0<z.im) : lowerNodeLog z=Complex.log z := by
  obtain ⟨hl,hr⟩ := upper_arg_range (z:=z) hz
  have hn : z≠0 := by intro e; simp [e] at hz
  have harg : (-I).arg+z.arg ∈ Ioc (-π) π := by rw [Complex.arg_neg_I]; constructor <;> linarith [pi_pos]
  rw [lowerNodeLog,Complex.log_mul (neg_ne_zero.mpr I_ne_zero) hn harg]
  simp [Complex.log,Complex.arg_neg_I]

theorem upperNodeLog_principal {z : ℂ} (hz : z.im<0) : upperNodeLog z=Complex.log z := by
  have hr := Complex.arg_neg_iff.mpr hz
  have hn : z≠0 := by intro e; simp [e] at hz
  have harg : I.arg+z.arg∈Ioc (-π) π := by rw [Complex.arg_I]; constructor <;> linarith [Complex.neg_pi_lt_arg z,pi_pos]
  rw [upperNodeLog,Complex.log_mul I_ne_zero hn harg,Complex.log_I]
  push_cast; ring

theorem vertical_log_norm {w : ℂ} (hL : 3≤Real.log ‖w‖) :
    ‖lowerNodeLog w‖≤Real.log ‖w‖+π ∧ ‖upperNodeLog w‖≤Real.log ‖w‖+π := by
  have h (f : ℂ) (he : f.re=Real.log ‖w‖) (hm : |f.im|≤3*π/2) : ‖f‖≤Real.log ‖w‖+π := by
    have hs := sq_le_sq' (abs_le.mp hm).1 (abs_le.mp hm).2
    have hπ := Real.pi_lt_four
    have hnorm := Complex.sq_norm f
    rw [Complex.normSq_apply,he] at hnorm
    nlinarith only [hs,hnorm,mul_le_mul_of_nonneg_right hL pi_pos.le,mul_lt_mul_of_pos_right hπ pi_pos,
      norm_nonneg f,pi_pos,hL]
  constructor
  · apply h
    · simp [lowerNodeLog,Complex.mul_re,Complex.log_re,norm_mul]
    · simp only [lowerNodeLog,Complex.add_im,Complex.log_im,Complex.mul_I_im,Complex.ofReal_re]
      apply abs_le.mpr
      constructor <;> linarith [Complex.neg_pi_lt_arg (-I*w),Complex.arg_le_pi (-I*w),pi_pos]
  · apply h
    · simp [upperNodeLog,Complex.mul_re,Complex.log_re,norm_mul]
    · simp only [upperNodeLog,Complex.sub_im,Complex.log_im,Complex.mul_I_im,Complex.ofReal_re]
      apply abs_le.mpr
      constructor <;> linarith [Complex.neg_pi_lt_arg (I*w),Complex.arg_le_pi (I*w),pi_pos]

/-- Both tails are on the real axis. The estimate permits nodes to be on
either side, as can happen after moving the compact part of the contour. -/
theorem vertical_log_tail {X x : ℝ} {c : ℂ} (hX : 10^18≤X) (hc : 4*‖c‖<X) (hx : X≤|x|) :
    |x|/2 ≤ ‖(x:ℂ)-c‖ ∧ ‖(x:ℂ)-c‖ ≤ 3*|x|/2 ∧
    ‖lowerNodeLog ((x:ℂ)-c)‖≤Real.log (3*|x|/2)+π ∧
    ‖upperNodeLog ((x:ℂ)-c)‖≤Real.log (3*|x|/2)+π := by
  have hl := norm_sub_le_norm_sub_add_norm_sub (x:ℂ) c 0
  have hr := norm_sub_le (x:ℂ) c
  simp only [sub_zero,Complex.norm_real,Real.norm_eq_abs] at hl hr
  have ha := abs_nonneg x
  have h₁ : |x|/2 ≤ ‖(x:ℂ)-c‖ := by linarith
  have h₂ : ‖(x:ℂ)-c‖ ≤ 3*|x|/2 := by linarith
  have hn : 0<‖(x:ℂ)-c‖ := by linarith
  have he : Real.exp 3 ≤ 27 := by
    rw [show (3:ℝ)=1+1+1 by norm_num,Real.exp_add,Real.exp_add]
    nlinarith only [pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 3]
  have hlog : 3≤Real.log ‖(x:ℂ)-c‖ := (Real.le_log_iff_exp_le hn).mpr (by linarith)
  have h := vertical_log_norm hlog
  have inc := add_le_add (Real.log_le_log hn h₂) (le_refl π)
  exact ⟨h₁,h₂,h.1.trans inc,h.2.trans inc⟩

end Liu
