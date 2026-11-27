module

public import Liu.Pick

@[expose] public section

noncomputable section
open Finset
namespace Liu

def singleConstant : ℝ := (3/4:ℝ)*∑' n : ℕ, 1 / (n:ℝ)^3

theorem single_margin_lower : (79/1000:ℝ) < singleConstant - k₀ := by
  have hs := Real.summable_one_div_nat_pow (p := 3) |>.mpr (by decide)
  have hl := hs.sum_le_tsum (Finset.range 101) (fun n _ => by positivity)
  have rational :
      (79/1000:ℚ) + (31416/10000:ℚ)^2/12 <
      (3/4:ℚ) * ∑ n ∈ Finset.range 101, 1/(n:ℚ)^3 := by decide +kernel
  have bound := (Rat.cast_lt (K := ℝ)).mpr rational
  push_cast at bound
  have hpi := Real.pi_lt_d4
  unfold singleConstant k₀
  nlinarith [sq_nonneg Real.pi,Real.pi_pos,
    mul_nonneg (sub_nonneg.mpr hpi.le) (show 0 ≤ 3.1416 + Real.pi by positivity)]

theorem log_mass_ratio_bounds {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : max a b / 4096 < min a b) :
    Real.log (b/a) ∈ Set.Icc (-(25/3:ℝ)) (25/3) := by
  have hab : a/4096 < b := (div_le_div_of_nonneg_right (le_max_left a b) (by norm_num)).trans_lt
    (h.trans_le (min_le_right a b))
  have hba : b/4096 < a := (div_le_div_of_nonneg_right (le_max_right a b) (by norm_num)).trans_lt
    (h.trans_le (min_le_left a b))
  have hu : b/a < (2:ℝ)^12 := (div_lt_iff₀ ha).mpr (by linarith)
  have hv : a/b < (2:ℝ)^12 := (div_lt_iff₀ hb).mpr (by linarith)
  have up := Real.log_lt_log (div_pos hb ha) hu
  have dn := Real.log_lt_log (div_pos ha hb) hv
  rw [Real.log_pow] at up dn
  rw [Real.log_div hb.ne' ha.ne'] at up ⊢
  rw [Real.log_div ha.ne' hb.ne'] at dn
  norm_num at up dn
  constructor <;> linarith [Real.log_two_lt_d9]

theorem Pair.coincident_value (p : Pair) (he : p.w₁ = p.w₂) :
    p.value = pole p.mass p.w₁ := by
  funext z
  simp only [Pair.value,pole,Pair.mass,Complex.ofReal_add,← he]
  ring

/-- The quantitative last step of the normalized small-mass proof. -/
theorem small_mass_arithmetic {x : ℝ} (hx : 0 < x) (hx' : x ≤ 1/4096) :
    (38/1000:ℝ) < (singleConstant-k₀) - x*(167-2*(singleConstant-k₀)) -
      x^2*(520+111*Real.log (2/x)) := by
  have hmargin := single_margin_lower
  have hp : 0 < singleConstant-k₀ := by linarith
  have hlog : Real.log (2/x) ≤ Real.log (8192:ℝ) + (1/(4096*x)-1) := by
    have heq : 2/x = 8192 * (1/(4096*x)) := by field_simp; ring
    rw [heq,Real.log_mul (by norm_num) (by positivity)]
    linarith [Real.log_le_sub_one_of_pos (x := 1/(4096*x)) (by positivity)]
  have h8192 : Real.log (8192:ℝ) < 10 := by
    have heq : (8192:ℝ) = 2^13 := by norm_num
    rw [heq,Real.log_pow]
    norm_num
    linarith [Real.log_two_lt_d9]
  have ht := mul_le_mul_of_nonneg_left hlog (sq_nonneg x)
  have heq : x^2 * (1/(4096*x)) = x/4096 := by field_simp
  have hxsq : x^2 ≤ (1/4096:ℝ)^2 := pow_le_pow_left₀ hx.le hx' 2
  have hb : x^2 * Real.log (2/x) ≤ 9 * x^2 + x/4096 := by
    nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr h8192.le)]
  nlinarith [mul_pos hx hp]

end Liu
