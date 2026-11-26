import Liu.FrozenGreen

noncomputable section
open Set MeasureTheory Real
open scoped ComplexConjugate
namespace Liu

theorem greenOperator_congr {f g : ℂ → ℂ} (h : EqOn f g upper) (z : ℂ) :
    greenOperator f z = greenOperator g z := by
  unfold greenOperator upperArea
  congr 1
  exact setIntegral_congr_fun upper_open.measurableSet (fun w hw => by rw [h hw])

theorem greenOperator_const_mul (a : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    greenOperator (fun w => a*f w) z = a*greenOperator f z := by
  unfold greenOperator
  simp_rw [mul_left_comm (greenLog z _:ℂ) a,integral_const_mul,Complex.real_smul]
  ring

theorem greenOperator_sub {f g : ℂ → ℂ} {z : ℂ}
    (hf : Integrable (fun w => (greenLog z w:ℂ)*f w) upperArea)
    (hg : Integrable (fun w => (greenLog z w:ℂ)*g w) upperArea) :
    greenOperator (fun w => f w-g w) z = greenOperator f z-greenOperator g z := by
  simp only [greenOperator,mul_sub,integral_sub hf hg,smul_sub]

theorem greenOperator_conj (f : ℂ → ℂ) (z : ℂ) :
    greenOperator (fun w => conj (f w)) z = conj (greenOperator f z) := by
  unfold greenOperator
  simp only [Complex.real_smul,map_mul,Complex.conj_ofReal,←integral_conj]

theorem PickSum.frozenGreen_lipschitz_zero {n : ℕ} (p : PickSum n) :
    ∃ C ≥ 0, ∀ t ∈ Icc (0:ℝ) 1, ∀ z : ℂ, 0≤z.im →
      ‖greenOperator (p.frozenError t) z-greenOperator (p.frozenError 0) z‖ ≤ t*(C*z.im/(1+‖z‖)^2) := by
  obtain ⟨A,hA,ha⟩ := p.parameterFactor_sub_one
  obtain ⟨B,hB,hb⟩ := p.logSource_conjugation_defect
  obtain ⟨C,hC,h⟩ := green_log_quartic_estimate (mul_nonneg hA.le hB.le)
  obtain ⟨_,_,hint⟩ := p.frozenGreen_estimate
  refine ⟨C,hC,?_⟩
  intro t ht z hz
  rcases eq_or_lt_of_le ht.1 with he | ht0
  · simp [←he]
  let q := fun w => (t:ℂ)⁻¹*(p.frozenError t w-p.frozenError 0 w)
  have hq : Measurable q := measurable_const.mul ((p.frozenError_measurable t).1.sub (p.frozenError_measurable 0).1)
  have hqt (w : ℂ) : (t:ℂ)*q w = p.frozenError t w-p.frozenError 0 w := by
    dsimp [q]
    rw [←mul_assoc,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr ht0.ne'),one_mul]
  have hdec (w : ℂ) (hw : w ∈ upper) : ‖q w‖ ≤ (A*B)*(1+log (2+‖w‖))/(1+‖w‖)^4 := by
    apply (le_of_mul_le_mul_left _ ht0)
    rw [←Complex.norm_of_nonneg ht.1,←norm_mul,hqt,p.frozenError_factor t (le_of_lt hw),
      p.frozenError_factor 0 (le_of_lt hw),show p.parameterFactor 0 w=1 by simp [PickSum.parameterFactor,PickSum.power],
      map_one,←sub_mul,←map_one (starRingEnd ℂ),←map_sub,norm_mul,Complex.norm_conj]
    have hlog := log_nonneg (show 1≤2+‖w‖ by linarith [norm_nonneg w])
    calc
      _ ≤ (t*(A*(1+log (2+‖w‖))))*(B/(1+‖w‖)^4) :=
        mul_le_mul (ha t ht w (le_of_lt hw)) (hb w (le_of_lt hw)) (norm_nonneg _) (by have := ht.1; positivity)
      _ = _ := by rw [Complex.norm_of_nonneg ht.1]; ring
  have hi t' (ht' : t' ∈ Icc (0:ℝ) 1) :=
    (hint t' ht' (p.frozenError t') (by simp) z hz).1
  rw [←greenOperator_sub (hi t ht) (hi 0 (by constructor <;> norm_num)),
    show (fun w => p.frozenError t w-p.frozenError 0 w) = (fun w => (t:ℂ)*q w) by funext w; exact (hqt w).symm,
    greenOperator_const_mul,norm_mul,Complex.norm_of_nonneg ht.1]
  exact mul_le_mul_of_nonneg_left (h q hq hdec z hz).2 ht.1

/-- At the critical exponent the source defect and its Green potential are imaginary. -/
theorem PickSum.green_error_zero_conj {n : ℕ} (p : PickSum n) (z : ℂ) :
    conj (greenOperator (p.frozenError 0) z) = -greenOperator (p.frozenError 0) z := by
  rw [←greenOperator_conj,←neg_one_mul (greenOperator _ _),←greenOperator_const_mul]
  apply greenOperator_congr
  intro w hw
  change conj (p.frozenError 0 w) = -1 * p.frozenError 0 w
  rw [p.frozenError_factor 0 (le_of_lt hw)]
  simp [PickSum.parameterFactor,PickSum.power]

end Liu
