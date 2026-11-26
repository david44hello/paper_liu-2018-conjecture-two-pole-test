import Mathlib

noncomputable section
open Set Real Metric Complex
open scoped Topology Interval Real
namespace Liu

/-- The closed ellipse with foci ±1, specified by its sum of focal
distances. Its major axis length is ρ+1/ρ. -/
def bernsteinEllipse (ρ : ℝ) : Set ℂ := {z | ‖z-1‖+‖z+1‖≤ρ+ρ⁻¹}

def joukowski (z : ℂ) : ℂ := (z+z⁻¹)/2

theorem joukowski_focal_sum {z : ℂ} (hz : z≠0) :
    ‖joukowski z-1‖+‖joukowski z+1‖=‖z‖+‖z‖⁻¹ := by
  have h₁ : joukowski z-1=(z-1)^2/(2*z) := by unfold joukowski; field_simp [hz]; ring
  have h₂ : joukowski z+1=(z+1)^2/(2*z) := by unfold joukowski; field_simp [hz]; ring
  have hp : ‖z-1‖^2+‖z+1‖^2=2*(‖z‖^2+1) := by
    simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.add_re,
      Complex.one_re,Complex.sub_im,Complex.add_im,Complex.one_im,sub_zero,add_zero]
    ring
  rw [h₁,h₂,norm_div,norm_div,norm_mul,Complex.norm_ofNat,norm_pow,norm_pow,←add_div,hp]
  field_simp [(norm_ne_zero_iff.mpr hz)] <;> ring

theorem joukowski_mem_ellipse {ρ : ℝ} (hρ : 1<ρ) {z : ℂ}
    (h₁ : ρ⁻¹≤‖z‖) (h₂ : ‖z‖≤ρ) : joukowski z∈bernsteinEllipse ρ := by
  have hr := zero_lt_one.trans hρ
  have hz := (inv_pos.mpr hr).trans_le h₁
  change ‖joukowski z-1‖+‖joukowski z+1‖≤_
  rw [joukowski_focal_sum (norm_pos_iff.mp hz)]
  have hp : 1≤ρ*‖z‖ := by
    have h := mul_le_mul_of_nonneg_left h₁ hr.le
    rwa [mul_inv_cancel₀ hr.ne'] at h
  have h := mul_nonneg (sub_nonneg.mpr h₂) (sub_nonneg.mpr hp)
  field_simp [hr.ne',hz.ne']
  nlinarith only [h]

def ellipseCoefficient (χ : ℂ → ℂ) (n : ℕ) : ℂ :=
  (2*π*I:ℂ)⁻¹ • ∮ z in C(0,1), χ (joukowski z)/z^(n+1)

/-- Cauchy's estimate on the actual outer ellipse. The coefficient is
computed on the unit circle and the contour moves through the full annulus. -/
theorem ellipse_coefficient_bound {χ : ℂ → ℂ} {ρ M : ℝ} (hρ : 1<ρ)
    (ha : AnalyticOnNhd ℂ χ (bernsteinEllipse ρ)) (hM : ∀ z∈bernsteinEllipse ρ, ‖χ z‖≤M)
    (n : ℕ) : ‖ellipseCoefficient χ n‖≤M/ρ^n := by
  let g := fun z : ℂ => χ (joukowski z)/z^(n+1)
  let A := closedBall (0:ℂ) ρ \ ball 0 1
  have hr := zero_lt_one.trans hρ
  have hi : ρ⁻¹≤1 := inv_le_one_of_one_le₀ hρ.le
  have hd (z : ℂ) (hz : z∈A) : DifferentiableAt ℂ g z := by
    have h₁ : 1≤‖z‖ := by simpa using hz.2
    have h₂ : ‖z‖≤ρ := by simpa using hz.1
    have hn := norm_pos_iff.mp (zero_lt_one.trans_le h₁)
    have hj : DifferentiableAt ℂ joukowski z := by unfold joukowski; fun_prop (disch := assumption)
    exact ((ha _ (joukowski_mem_ellipse hρ (hi.trans h₁) h₂)).differentiableAt.comp _ hj).div
      ((differentiableAt_id.pow _)) (pow_ne_zero _ hn)
  have he := Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable (f:=g) (c:=0)
    zero_lt_one hρ.le (countable_empty (α:=ℂ)) (fun z hz => (hd z hz).continuousAt.continuousWithinAt)
    (fun z hz => hd z ⟨ball_subset_closedBall hz.1.1,fun h => hz.1.2 (ball_subset_closedBall h)⟩)
  change ‖(2*π*I:ℂ)⁻¹ • ∮ z in C(0,1), g z‖≤_
  rw [←he]
  apply (circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const (C:=M/ρ^(n+1)) hr.le ?_).trans_eq
  · field_simp [hr.ne'] <;> ring
  · intro z hz
    have hnorm : ‖z‖=ρ := by simpa using hz
    have hj := joukowski_mem_ellipse hρ (z:=z) (hnorm ▸ (hi.trans hρ.le)) hnorm.le
    rw [show g z=χ (joukowski z)/z^(n+1) from rfl,norm_div,norm_pow,hnorm]
    exact div_le_div_of_nonneg_right (hM _ hj) (pow_nonneg hr.le _)

end Liu
