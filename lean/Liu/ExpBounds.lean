import Mathlib

namespace Liu.Certificate

/-- Taylor polynomial and a two-sided exponential remainder majorant on [-1,1]. -/
def expSmallUpper (x : ℚ) : ℚ :=
  (∑ k ∈ Finset.range 8, x^k / k.factorial) + |x|^8 * (9 / 322560)

/-- Round upward to avoid growth of the denominators when the result is raised to a power. -/
def roundUp (q : ℚ) : ℚ := (⌈q * 10000000⌉ : ℤ) / 10000000

theorem le_roundUp (q : ℚ) : q ≤ roundUp q := by
  unfold roundUp
  rw [le_div_iff₀ (by norm_num : (0:ℚ) < 10000000)]
  exact Int.le_ceil _

def expUpper (q : ℚ) : ℚ := (roundUp (expSmallUpper (q/16)))^16

theorem expSmallUpper_sound (q : ℚ) (h : |q| ≤ 1) :
    Real.exp (q:ℝ) ≤ (expSmallUpper q : ℝ) := by
  have ht := Real.exp_bound (x := (q:ℝ)) (n := 8) (by exact_mod_cast h) (by decide)
  have hu := (abs_le.mp ht).2
  unfold expSmallUpper
  push_cast
  norm_num [Nat.factorial] at hu
  linarith

theorem expUpper_sound (q : ℚ) (h : |q| ≤ 16) : Real.exp (q:ℝ) ≤ (expUpper q : ℝ) := by
  have hsmall : |q/16| ≤ 1 := by rw [abs_div]; norm_num; linarith
  have hs := expSmallUpper_sound (q/16) hsmall
  have hu : Real.exp ((q/16:ℚ):ℝ) ≤ (roundUp (expSmallUpper (q/16)):ℝ) :=
    hs.trans (by exact_mod_cast le_roundUp (expSmallUpper (q/16)))
  have power := pow_le_pow_left₀ (Real.exp_pos _).le hu 16
  rw [← Real.exp_nat_mul] at power
  push_cast at power
  convert power using 1 <;> push_cast [expUpper] <;> ring_nf

theorem exp_neg_half_upper : Real.exp (-(1/2:ℝ)) ≤ (606530660/1000000000:ℝ) := by
  have he := Real.exp_bound (x := -(1/2:ℝ)) (n := 12) (by norm_num) (by decide)
  have hu := (abs_le.mp he).2
  norm_num [Finset.sum_range_succ, Nat.factorial] at hu
  linarith

theorem sin_one_lower : (841/1000:ℝ) ≤ Real.sin 1 := by
  have h₁ := Real.sin_ge_sub_cube (x := (1/3:ℝ)) (by norm_num)
  have h₂ := (abs_le.mp (Real.sin_bound (x := (1/3:ℝ)) (by norm_num))).2
  have hp : 0 ≤ Real.sin (1/3:ℝ) := by linarith
  have hs : Real.sin (1/3:ℝ) ≤ 32721/100000 := by norm_num at h₂; linarith
  have hpow := pow_le_pow_left₀ hp hs 3
  have ident := Real.sin_three_mul (1/3:ℝ)
  norm_num at ident h₁ hpow
  linarith

theorem sin_053_lower : (5054/10000:ℝ) ≤ Real.sin (53/100:ℝ) := by
  have h₁ := Real.sin_ge_sub_cube (x := (53/300:ℝ)) (by norm_num)
  have h₂ := (abs_le.mp (Real.sin_bound (x := (53/300:ℝ)) (by norm_num))).2
  have hp : 0 ≤ Real.sin (53/300:ℝ) := by linarith
  have hs : Real.sin (53/300:ℝ) ≤ 17575/100000 := by norm_num at h₂; linarith
  have hpow := pow_le_pow_left₀ hp hs 3
  have ident := Real.sin_three_mul (53/300:ℝ)
  norm_num at ident h₁ hpow
  linarith

end Liu.Certificate
