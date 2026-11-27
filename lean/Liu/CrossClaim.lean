module

public import Liu.CrossSource
public import Liu.Prefix

@[expose] public section

noncomputable section
open scoped ComplexConjugate
namespace Liu

theorem direction_norm (γ : ℝ) : ‖direction γ‖ = 1 := by
  simp [direction,Complex.norm_exp]

theorem direction_im (γ : ℝ) : (direction γ).im = -Real.sin γ := by
  simp [direction,Complex.exp_im,Complex.mul_im,Complex.mul_re]

theorem direction_perp (z : ℂ) (γ : ℝ) :
    (z*conj (direction γ)).im = z.re*Real.sin γ + z.im*Real.cos γ := by
  simp [direction,Complex.mul_im,Complex.exp_re,Complex.exp_im,Complex.mul_re]

/-- All parts of the cross-source identity on its open half-plane of integration.
The derivative in crossSource is the actual derivative of the rational Pick sum. -/
theorem cross_source_claim (s γ : ℝ) (hγ : γ ∈ Set.Icc 0 (Real.pi/2))
    {z : ℂ} (hz : 0 < z.im) :
    let a := normalMass s
    let q := direction γ
    let Y := z.re*Real.sin γ + z.im*Real.cos γ
    let D := ‖z‖^2*‖z-q‖^2
    crossSource a q z = (2*Complex.I*(a:ℂ)*(1-a)*conj q*(Y:ℂ)) /
      ((D:ℂ)*(conj z-(a:ℂ)*conj q)) ∧
    (crossSource a q z).re = -2*a*(1-a)*Y^2/(D*‖z-(a:ℂ)*q‖^2) ∧
    (crossSource a q z).re ≤ 0 ∧
    ‖crossSource a q z‖ = 2*a*(1-a)*|Y| / (D*‖z-(a:ℂ)*q‖) ∧
    |Y| ≤ min ‖z‖ (min ‖z-q‖ ‖z-(a:ℂ)*q‖) := by
  dsimp only
  have ha := Certificate.normalMass_pos s
  have hb : normalMass s ≤ 1 := by
    linarith [Certificate.complement_normalMass s,Certificate.normalMass_pos (-s)]
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi hγ.1 (hγ.2.trans (by linarith [Real.pi_pos]))
  have nz : z ≠ 0 := by intro h; simp [h] at hz
  have sep (a : ℝ) (h : 0 ≤ a) : z-(a:ℂ)*direction γ ≠ 0 := by
    intro he
    have hi := congrArg Complex.im (sub_eq_zero.mp he)
    simp [direction_im,Complex.mul_im] at hi
    nlinarith [mul_nonneg h hsin]
  have hq : z - direction γ ≠ 0 := by simpa using sep 1 (by norm_num)
  have hc := sep (normalMass s) ha.le
  have re := crossSource_real (direction_norm γ) nz hq hc
  rw [direction_perp] at re
  refine ⟨?_,re,?_,?_,cross_source_three_distances z (normalMass s) γ⟩
  · simpa only [direction_perp] using crossSource_formula nz hq hc
  · rw [re]
    have hb' := sub_nonneg.mpr hb
    have hnum : 0 ≤ 2*normalMass s*(1-normalMass s)*(z.re*Real.sin γ+z.im*Real.cos γ)^2 := by positivity
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    linarith
  · simpa only [direction_perp] using crossSource_abs ha.le hb (direction_norm γ) nz hq hc

theorem edgeSum_is_normal (s γ : ℝ) :
    normalSum s γ 0 = edgeSum (normalMass s) (direction γ) := by
  funext z
  simp [normalSum, pole, edgeSum, sub_eq_add_neg,neg_div]
  ring

theorem crossSource_is_actual (s γ : ℝ) (z : ℂ) :
    crossSource (normalMass s) (direction γ) z =
      -2*Complex.I*source (normalSum s γ 0) z -
        (normalMass s/‖z‖^2:ℝ) - ((1-normalMass s)/‖z-direction γ‖^2:ℝ) := by
  rw [edgeSum_is_normal]
  unfold crossSource source
  have hi := Complex.I_sq
  linear_combination (edgeSum (normalMass s) (direction γ) z /
    conj (edgeSum (normalMass s) (direction γ) z) *
    conj (deriv (edgeSum (normalMass s) (direction γ)) z)) * hi

end Liu
