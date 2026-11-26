import Liu.Pick

noncomputable section
open scoped ComplexConjugate
namespace Liu

/-- First-order terms cancel at the mass centre in the merged-pole estimate. -/
theorem barycentric_cancellation {x e₁ e₂ μ₁ μ₂ : ℂ}
    (hx : x ≠ 0) (h₁ : x-e₁ ≠ 0) (h₂ : x-e₂ ≠ 0)
    (hcenter : μ₁*e₁+μ₂*e₂=0) :
    μ₁*e₁/(x-e₁) + μ₂*e₂/(x-e₂) =
    μ₁*e₁^2/(x*(x-e₁)) + μ₂*e₂^2/(x*(x-e₂)) := by
  have split (e μ : ℂ) (h : x-e ≠ 0) :
      μ*e/(x-e) = μ*e/x + μ*e^2/(x*(x-e)) := by
    field_simp
    ring
  rw [split e₁ μ₁ h₁,split e₂ μ₂ h₂]
  linear_combination (1/x)*hcenter

/-- Quantitative smallness which allows the argument of 1+η to be taken on a single branch. -/
theorem cluster_scalar_bound {μ ν d u : ℝ} (hμ : 0 ≤ μ) (hν : 0 ≤ ν)
    (hm : μ+ν=1) (hd : 0 ≤ d) (hu : 0 < u) (hdu : d ≤ u/4) :
    μ*ν*d^2 / (u*(u-d)) ≤ 1/48 := by
  have hm' : μ*ν ≤ 1/4 := by nlinarith [sq_nonneg (μ-ν), sq_nonneg (μ+ν-1)]
  have hp : 0 < u*(u-d) := mul_pos hu (by linarith)
  apply (div_le_iff₀ hp).mpr
  have hdsq : d^2 ≤ (u/4)^2 := pow_le_pow_left₀ hd hdu 2
  nlinarith [mul_le_mul_of_nonneg_right hm' (sq_nonneg d),mul_le_mul_of_nonneg_left hdu hu.le]

/-- The perpendicular component is common to all points on the line of the three nodes. -/
theorem rotated_distance_bound (z q : ℂ) (a : ℝ) (hq : ‖q‖ = 1) :
    |(z*conj q).im| ≤ ‖z-(a:ℂ)*q‖ := by
  have hn : q * conj q = 1 := by
    rw [Complex.mul_conj,Complex.normSq_eq_norm_sq,hq]
    norm_num
  have im_eq : ((z-(a:ℂ)*q)*conj q).im = (z*conj q).im := by
    rw [sub_mul,mul_assoc,hn,mul_one]
    simp
  rw [← im_eq]
  calc
    _ ≤ ‖(z-(a:ℂ)*q)*conj q‖ := Complex.abs_im_le_norm _
    _ = _ := by simp [norm_mul,hq]

theorem cross_source_three_distances (z : ℂ) (a γ : ℝ) :
    |z.re * Real.sin γ + z.im * Real.cos γ| ≤
      min ‖z‖ (min ‖z-direction γ‖ ‖z-(a:ℂ)*direction γ‖) := by
  have hq : ‖direction γ‖ = 1 := by simp [direction,Complex.norm_exp]
  have eqn : (z*conj (direction γ)).im = z.re * Real.sin γ + z.im * Real.cos γ := by
    simp [direction,Complex.mul_im,Complex.exp_re,Complex.exp_im,Complex.mul_re]
  rw [← eqn,le_min_iff,le_min_iff]
  exact ⟨by simpa using rotated_distance_bound z (direction γ) 0 hq,
         by simpa using rotated_distance_bound z (direction γ) 1 hq,
         rotated_distance_bound z (direction γ) a hq⟩

end Liu
