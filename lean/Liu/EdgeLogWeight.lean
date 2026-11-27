module

public import Liu.IsolatedMoment

@[expose] public section

noncomputable section
open Set Real MeasureTheory
namespace Liu

def halfLogWeight (x : ℝ) := (Ioc (0:ℝ) 1).indicator (fun t => t^(-(1/2:ℝ))) x
def edgeLogWeight (x : ℝ) := halfLogWeight x+halfLogWeight (-x)

theorem edgeLogWeight_nonneg (x : ℝ) : 0≤edgeLogWeight x := by
  have hn (y : ℝ) : 0≤halfLogWeight y := indicator_nonneg (fun t ht => rpow_nonneg (le_of_lt ht.1) _) _
  exact add_nonneg (hn x) (hn (-x))

theorem edgeLogWeight_mass : Integrable edgeLogWeight ∧ ∫ x, edgeLogWeight x = 4 := by
  have he : (∫ x, halfLogWeight x)=2 := by
    unfold halfLogWeight
    rw [integral_indicator measurableSet_Ioc,←intervalIntegral.integral_of_le zero_le_one,
      integral_rpow (Or.inl (by norm_num))]
    norm_num
  have hi : Integrable halfLogWeight := Integrable.of_integral_ne_zero (he ▸ (by norm_num))
  have hj := hi.comp_neg
  refine ⟨hi.add hj,?_⟩
  unfold edgeLogWeight
  rw [integral_add hi hj,integral_neg_eq_self,he]; norm_num

theorem edgeLogWeight_value {x : ℝ} (hx : 0 < |x|) (h₁ : |x|≤1) :
    edgeLogWeight x=(sqrt |x|)⁻¹ := by
  rcases lt_or_gt_of_ne (abs_pos.mp hx) with h|h
  · rw [abs_of_neg h] at hx h₁ ⊢
    simp [edgeLogWeight,halfLogWeight,h.not_gt,hx,h₁,sqrt_eq_rpow,rpow_neg hx.le]
  · rw [abs_of_pos h] at h₁ ⊢
    simp [edgeLogWeight,halfLogWeight,h,h₁,h.not_gt,sqrt_eq_rpow,rpow_neg h.le]

theorem edge_log_sqrt_bound {r : ℝ} (hr : 0<r) : 1+log (1/r)≤2/(sqrt r) := by
  have hs := sqrt_pos.mpr hr
  have hh := log_le_sub_one_of_pos (inv_pos.mpr hs)
  rw [log_inv,log_sqrt hr.le] at hh
  rw [one_div,log_inv,div_eq_mul_inv]
  linarith

theorem edge_log_square_bound {u : ℝ} (hu : 0<u) (h₁ : u≤1) : u*(1+log (1/u))^2≤4 := by
  have hh : 0≤1+log (1/u) := by linarith [log_nonneg ((one_le_div hu).mpr h₁)]
  have hp := pow_le_pow_left₀ hh (edge_log_sqrt_bound hu) 2
  rw [div_pow,sq_sqrt hu.le] at hp
  have he := (le_div_iff₀ hu).mp hp
  linarith

end Liu
