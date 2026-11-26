import Liu.PickSums

noncomputable section
open scoped ComplexConjugate
open MeasureTheory Set
namespace Liu

theorem pole_hasDerivAt {a : ℝ} {z w : ℂ} (h : z≠w) :
    HasDerivAt (pole a w) ((a:ℂ)/(z-w)^2) z := by
  have d := (hasDerivAt_const z (-(a:ℂ))).div ((hasDerivAt_id z).sub_const w) (sub_ne_zero.mpr h)
  convert d using 1
  · rfl
  · simp

theorem PickSum.hasDerivAt {n : ℕ} (p : PickSum n) {z : ℂ} (hz : 0≤z.im) :
    HasDerivAt p.value (∑ i, (p.weight i:ℂ)/(z-p.location i)^2) z := by
  unfold PickSum.value
  apply HasDerivAt.fun_sum
  intro i _
  apply pole_hasDerivAt
  intro he
  rw [he] at hz
  linarith [p.below i]

theorem source_norm {S : ℂ → ℂ} {z : ℂ} (h : S z≠0) :
    ‖source S z‖ = ‖deriv S z‖/2 := by
  simp [source,norm_mul,norm_div,Complex.norm_conj,div_self (norm_ne_zero_iff.mpr h)]
  ring

def PickSum.derivativeBound {n : ℕ} (p : PickSum n) : ℝ :=
  ∑ i, p.weight i*(poleBound 1 (p.location i))^2

theorem PickSum.source_decay {n : ℕ} (p : PickSum n) {z : ℂ} (hz : 0≤z.im) :
    ‖source p.value z‖ ≤ (p.derivativeBound/2)/(1+‖z‖)^2 := by
  have hnz : p.value z ≠ 0 := fun he => by have hi := p.value_im_pos hz; simp [he] at hi
  rw [source_norm hnz,(p.hasDerivAt hz).deriv]
  have hb : ‖∑ i, (p.weight i:ℂ)/(z-p.location i)^2‖ ≤ p.derivativeBound/(1+‖z‖)^2 := by
    unfold derivativeBound
    rw [Finset.sum_div]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
    intro i _
    have hi := p.pos i
    have h1 := pole_global_decay (a := 1) (by norm_num) (p.below i) hz
    have hq := pow_le_pow_left₀ (norm_nonneg _) h1 2
    simp only [pole,norm_div,norm_neg,Complex.ofReal_one,norm_one,one_div,inv_pow,div_pow] at hq
    simp only [norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hi]
    calc
      _ = p.weight i * (‖z-p.location i‖ ^ 2)⁻¹ := by ring
      _ ≤ _ := by simpa [mul_div_assoc] using mul_le_mul_of_nonneg_left hq hi.le
  calc
    _ ≤ (p.derivativeBound/(1+‖z‖)^2)/2 := by linarith
    _ = _ := by ring

end Liu
